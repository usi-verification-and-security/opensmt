#!/usr/bin/env python
# -*- coding: utf-8 -*-

import subprocess
import socket
import optparse
import select
import struct
import threading
import signal
import sys
import time
import os
import pickle
import tempfile
import atexit
import json
import framework
import net
import logging
import traceback
import random
import sqlite3
import hashlib

__author__ = 'Matteo Marescotti'


class SocketParallelizationTree(framework.ParallelizationTree):
    reverse_types = (framework.SolveState, net.Socket, framework.Node)

    def __init__(self, name, hash, formula, config, conn=None, table_prefix=''):
        super().__init__(name=name,
                         hash=hash,
                         formula=formula,
                         conn=conn,
                         table_prefix=table_prefix
                         )
        self._config = config

        if self._conn:
            self._conn.cursor().execute("CREATE TABLE IF NOT EXISTS {}SolvingHistory ("
                                        "id INTEGER NOT NULL PRIMARY KEY, "
                                        "ts INTEGER NOT NULL DEFAULT (strftime('%s', 'now')),"
                                        "instance TEXT NOT NULL, "
                                        "event TEXT NOT NULL, "
                                        "solver TEXT, "
                                        "node TEXT, "
                                        "data TEXT"
                                        ");".format(self._table_prefix))
            self._conn.cursor().execute("DELETE FROM {}SolvingHistory WHERE instance=?;".format(table_prefix), (
                self.name,
            ))
            self._conn.commit()
            self.db_log('CREATE')

        self._solvers = set()

    def new_node(self, cls, *args, **kwargs):
        node = super().new_node(cls, *args, **kwargs)
        node['active'] = True
        if issubclass(cls, framework.AndNode):
            node['solvers'] = node.observed(set)
        return node

    def prune(self, node):
        if node is self.root:
            self.db_log('SOLVED', None, None, {'status': node['status'].name})
        node['active'] = False
        if isinstance(node, framework.AndNode):
            self.assign_solvers(node['solvers'])
        for child in node['children']:
            self.prune(child)

    def solver_node(self, sock):
        if sock not in self.reverse:
            return
        for path in self.reverse[sock]:
            if len(path) > 1 and isinstance(path[-2], framework.AndNode) and sock in path[-2]['solvers']:
                return path[-2]

    # if socket is new then it is added
    # if node is none then auto assign
    # if node is False remove solver
    def assign_solvers(self, solvers=None, node=None):
        if solvers is None:
            solvers = {solver for solver in self._solvers if solver.tree is None}
        else:
            if not isinstance(solvers, (list, set, tuple)):
                solvers = {solvers}
            solvers = set(solvers)
            self._solvers.update(solvers)
        for solver in solvers:
            current_node = self.solver_node(solver)
            if current_node and node is not current_node:
                try:
                    solver.stop()
                except BaseException as ex:
                    self.db_log('ERROR',
                                solver,
                                current_node,
                                'exception during solver stop request: {}'.format(ex))
                current_node['solvers'].remove(solver)
        if node is False:
            # !!! check if the solver was asked to create partitions
            self._solvers.difference_update(solvers)
            return
        if self.root['status'] != framework.SolveState.unknown:
            return
        if isinstance(node, framework.AndNode):
            if node.observer is not self:
                raise ValueError
            for solver in solvers:
                try:
                    solver.solve(self, node)
                except BaseException as ex:
                    self.db_log('ERROR',
                                solver,
                                node,
                                'exception during solver solve request:{}'.format(ex))
                else:
                    node['solvers'].update(solvers)
        elif node is None:
            l = -1
            while solvers:
                l += 1
                if l % 2:
                    continue
                level = self.level(l)
                if not level:
                    break
                for node in level:
                    if node['active']:
                        while solvers and len(node['solvers']) < self._config.portfolio_max:
                            self.assign_solvers(solvers.pop(), node)

            if solvers:
                l = -1
                reserved = len(solvers)
                while True:
                    l += 1
                    if l % 2:
                        continue
                    level = self.level(l)
                    if not level:
                        break
                    children = self._level_children(l)

                    for node in level:
                        if reserved <= 0:
                            break
                        if len(node['children']) < children:
                            for i in range(min(len(node['solvers']), children - len(node['children']))):
                                partition_solver = random.sample(node['solvers'], 1)[0]
                                try:
                                    partition_solver.ask_partitions(self._level_children(l + 1))
                                except BaseException as ex:
                                    self.db_log('ERROR',
                                                partition_solver,
                                                node,
                                                'exception during solver ask for partitions: {}'.format(ex))
                                else:
                                    reserved -= 1
                    if reserved <= 0:
                        break
        else:
            raise ValueError

    def db_log(self, event, solver=None, node=None, data=None):
        if not self._conn:
            return
        self._conn.cursor().execute("INSERT INTO {}SolvingHistory (instance, event, solver, node, data) "
                                    "VALUES (?,?,?,?,?)".format(self._table_prefix), (
                                        self.name,
                                        event,
                                        str(solver.remote_address) if solver else None,
                                        str(self.node_path(node, keys=True)) if node else None,
                                        json.dumps(data) if data else None
                                    ))
        self._conn.commit()

    def _level_children(self, level):
        if level < len(self._config.partition_policy):
            return self._config.partition_policy[level]
        elif len(self._config.partition_policy) > 1:
            return self._config.partition_policy[-2]
        elif len(self._config.partition_policy) > 0:
            return self._config.partition_policy[-1]
        else:
            raise ValueError('invalid partition policy')


class Solver(net.Socket):
    def __init__(self, sock, data):
        super().__init__(sock._sock)
        self.data = data
        self.tree = None
        self.node = None
        self.or_nodes = []

    def solve(self, tree, node):
        if self.node:
            raise ValueError('already solving')
        self.write({
            'command': 'solve',
            'hash': tree.node_hash(node),
            'name': tree.name
        }, node.formula.smt)
        self.tree, self.node = tree, node
        self.tree.db_log('+', self, node)

    def stop(self):
        if self.node is None:
            raise ValueError('not solving anything')
        self.write({
            'command': 'stop',
            'hash': self.tree.node_hash(self.node),
            'name': self.tree.name
        }, '')
        self.tree.db_log('-', self, self.node)
        self.tree = self.node = None
        self.or_nodes = []

    def ask_partitions(self, n, node=None):
        if self.node is None:
            raise ValueError('not solving anything')
        self.write({
            'command': 'partitions',
            'hash': self.tree.node_hash(self.node),
            'name': self.tree.name,
            'partitions': n
        }, '')
        if node is None:
            node = self.node.add_child()  # CREATING OR NODE
        self.tree.db_log('OR', self, node)
        self.or_nodes.append(node)

    def read(self):
        try:
            header, message = super().read()
        except:
            if self.tree:
                self.tree.assign_solvers(self, False)
            raise
        if self.tree is None or self.node is None:
            return header, message
        if self.tree.name != header['name']:
            header['error'] = 'wrong instance "{}", expected "{}"'.format(
                header['name'],
                self.tree.name
            )
            return header, message
        if self.tree.node_hash(self.node) != header['hash']:
            header['error'] = 'wrong hash "{}", expected "{}"'.format(
                header['hash'],
                self.tree.node_hash(self.node)
            )
            return header, message

        if 'status' in header:
            status = framework.SolveState.__members__[header['status']]
            if status is framework.SolveState.unknown:
                header['error'] = 'wrong status "{}"'.format(header['status'])
                return header, message
            header['node'] = self.tree.node_path(self.node, keys=True)
            self.tree.db_log('STATUS', self, self.node, {'status': status.name})
            self.node['status'] = status
        elif 'partitions' in header and self.or_nodes:
            node = self.or_nodes.pop()
            try:
                partitions = []
                start = 0
                for i in range(int(header['partitions'])):
                    end = int(header[str(i)])
                    if end > len(message):
                        raise ValueError('bad partition index')
                    partitions.append(message[start:end])
                    start = end
                for partition in partitions:
                    child = node.add_child(framework.SMTFormula(partition))
                    self.tree.db_log('AND', self, child)
            except BaseException as ex:
                header['error'] = 'error reading partitions: {}'.format(ex)
                node['children'].clear()
                self.ask_partitions(header['partitions'], node)
                return header, message
            else:
                self.tree.assign_solvers()

        return header, message


class ParallelizationServer(net.Server):
    def __init__(self, port, config, conn=None, table_prefix='', logger=None):
        super().__init__(port, timeout=config.partition_timeout, logger=logger)
        self._config = config
        self._conn = conn
        self._table_prefix = table_prefix
        self._trees = []
        self._last = time.time()
        if self._conn:
            self._conn.cursor().execute("CREATE TABLE IF NOT EXISTS {}ServerLog ("
                                        "id INTEGER NOT NULL PRIMARY KEY, "
                                        "ts INTEGER NOT NULL DEFAULT (strftime('%s', 'now')),"
                                        "level TEXT NOT NULL,"
                                        "message TEXT NOT NULL,"
                                        "data TEXT"
                                        ");".format(self._table_prefix))
            cursor = self._conn.cursor()
            cursor.execute("DELETE FROM {}SolvingHistory;".format(table_prefix))
            cursor.execute("VACUUM;")
            self._conn.commit()
            self.log(logging.INFO, 'server start')

    def handle_accept(self, sock):
        self.log(logging.INFO, 'new connection from {}'.format(sock.remote_address))

    def handle_message(self, sock, header, message):
        if isinstance(sock, Solver):
            if 'error' in header:
                self.log(logging.ERROR, 'invalid message from solver {}. {}'.format(
                    sock.remote_address,
                    header['error']
                ), {'header': header, 'message': message.decode()})
            else:
                self.log(logging.INFO, 'message from solver {}'.format(
                    sock.remote_address
                ), {'header': header, 'message': message.decode()})
            return
        self.log(logging.INFO, 'message from {}'.format(sock.remote_address))
        if 'command' in header:
            if header['command'] == 'solve':
                try:
                    instance, hash = self._check(header)
                except:
                    return
                self.log(logging.INFO, 'new instance "{}" with hash "{}"'.format(
                    instance,
                    hash
                ), {'header': header, 'message': message.decode()})
                self._trees.append(SocketParallelizationTree(
                    name=instance,
                    hash=hash,
                    config=self._config,
                    formula=framework.SMTFormula(message),
                    conn=self._conn,
                    table_prefix=self._table_prefix
                ))
                self.entrust()
        elif 'solver' in header:
            solver = Solver(sock, header)
            self.log(logging.INFO, 'new solver "{}" at {}'.format(
                solver.data['solver'],
                solver.remote_address
            ), {'header': header, 'message': message.decode()})
            self._rlist.remove(sock)
            self._rlist.add(solver)
            self.entrust()
        elif 'eval' in header:
            response_message = ''
            try:
                response_message = str(eval(header['eval']))
            except:
                response_message = str(traceback.format_exc())
            finally:
                sock.write({}, response_message)

    def handle_close(self, sock):
        if isinstance(sock, Solver):
            self.log(logging.INFO, 'connection closed from solver {}'.format(sock.remote_address))

    def handle_timeout(self):
        print()
        print('TIMEOUT: {}'.format(time.time()-self._last))
        self._last = time.time()
        print()

    # trees = [tree for tree in self._trees if tree.root['status'] == framework.SolveState.unknown]
    # if not trees:
    #     return
    # tree = trees[0]

    def entrust(self):
        trees = [tree for tree in self._trees if tree.root['status'] == framework.SolveState.unknown]
        if not trees:
            return
        tree = trees[0]
        for idle_solver in (solver for solver in self._rlist if
                            isinstance(solver, Solver) and solver.tree is None):
            tree.assign_solvers(idle_solver)

    def _check(self, header):
        if not (header.get('name') or header.get('hash')):
            self.log(logging.WARNING, 'incomplete instance received', {'header': header})
            raise ValueError
        instance = header.get('name', header.get('hash'))
        hash = header.get('hash', header.get('name'))
        return instance, hash

    def log(self, level, message, data=None):
        super().log(level, message)
        if not self._conn:
            return
        self._conn.cursor().execute("INSERT INTO {}ServerLog (level, message, data) "
                                    "VALUES (?,?,?)".format(self._table_prefix), (
                                        logging.getLevelName(level),
                                        message,
                                        json.dumps(data) if data else None
                                    ))
        self._conn.commit()


if __name__ == '__main__':
    class Config:
        portfolio_max = 1
        partition_timeout = 10
        partition_policy = [2, 2]


    logging.basicConfig(level=logging.WARNING, format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
    parser = optparse.OptionParser()
    parser.add_option('-c', '--config', dest='config', type='str',
                      action="callback",
                      callback=lambda option, opt_str, value, parser:
                      setattr(parser.values, option.dest, __import__(os.path.splitext(os.path.basename(value))[0])),
                      default=Config(), help='config file path')
    parser.add_option('-d', '--database', dest='db', type='str',
                      action="callback",
                      callback=lambda option, opt_str, value, parser:
                      setattr(parser.values, option.dest, sqlite3.connect(value)),
                      default=None, help='sqlite3 database file path')

    options, args = parser.parse_args()

    s = ParallelizationServer(port=3000, config=options.config, conn=options.db, logger=logging.getLogger('server'))
    try:
        s.run_forever()
    except KeyboardInterrupt:
        pass
