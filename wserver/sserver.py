#!/usr/bin/env python
# -*- coding: utf-8 -*-

import subprocess
import socket
import optparse
import select
import struct
import threading
import sys
import time
import os
import pickle
import tempfile

__author__ = 'Matteo Marescotti'


class Dict(dict):
    def keys_of(self, item):
        return [key for key in self if self[key] == item]


class Socket(socket.socket):
    address = None

    def __init__(self, sock=None):
        if sock:
            super(Socket, self).__init__(_sock=sock._sock)
        else:
            super(Socket, self).__init__(socket.AF_INET, socket.SOCK_STREAM)
            self.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)

    def accept(self):
        s, a = super(Socket, self).accept()
        s = Socket(s)
        s.address = a
        return s

    def bind(self, address):
        super(Socket, self).bind(address)
        self.address = address

    def read(self):
        content = ''
        length = self.recv(4)
        if len(length) == 4:
            length = struct.unpack('!I', length)[0]
            while len(content) < length:
                content += self.recv(length - len(content))
        return content

    def write(self, msg):
        length = len(msg)
        if length > 2 ** 32:
            raise ValueError
        self.send(struct.pack('!I', length))
        self.send(msg)

    def close(self):
        super(Socket, self).close()
        self.address = None


class Server(object):
    output = open('/dev/null', 'w')

    def __init__(self, port):
        self.address = ('0.0.0.0', port)
        self._socket = Socket()
        self._socket.bind(self.address)
        self._socket.listen(50)
        self._rlist = [self._socket]

    def handle_accept(self, sock):
        pass

    def handle_message(self, sock, message):
        pass

    def handle_close(self, sock):
        pass

    def handle_timeout(self):
        pass

    def run_forever(self):
        while True:
            rlist = select.select(self._rlist, [], [], 60)[0]
            if len(rlist) == 0:
                self.handle_timeout()
                continue
            for sock in rlist:
                if sock is self._socket:
                    new_socket = self._socket.accept()
                    self._rlist.append(new_socket)
                    self.handle_accept(new_socket)
                    continue
                try:
                    message = sock.read()
                except:
                    self.output.write('_ socket.error during read\n')
                    continue
                length = len(message)
                if length == 0:
                    self.handle_close(sock)
                    sock.close()
                    self._rlist.remove(sock)
                    continue
                self.handle_message(sock, message)


class Task(object):
    def __init__(self, code):
        self.code = code
        self.solved = False


class Job(dict):
    def __init__(self, name, tasks=None):
        super(Job, self).__init__()
        self.update({
            'name': name,
            'history': [('CREATED', time.time())],
        })
        if not tasks:
            tasks = (None,)
        self.tasks = tasks
        self.started = False

    def add_history_item(self, item):
        now = time.time()
        if item[0] == '+' and not self.started:
            self.started = now
        if item[0] == 'S':
            self['elapsed'] = now - self.started
            self['result'] = item[1]
        self['history'].append((now, item))


class WorkerServer(Server):
    _lock = threading.Lock()
    _status = {}  # sock -> (job, task_id)
    _jobs = Dict({
        -2: Job('\\ERROR'),
        -1: Job('\\IDLE')
    })

    def __init__(self, port, timeout):
        self._timeout = timeout
        super(WorkerServer, self).__init__(port)

    def handle_timeout(self):
        if not self._timeout:
            return
        jids = []
        with self._lock:
            min = time.time() - self._timeout
            for sock in self._status:
                job = self._status[sock][0]
                jid = self._jobs.keys_of(job)[0]
                if job.started and job.started < min:
                    jids.append(jid)
        for jid in jids:
            self.handle_command('Q{}'.format(jid))

    def handle_accept(self, sock):
        with self._lock:
            self.output.write('+ worker {}\n'.format(sock.address))
            self._status[sock] = (self._jobs[-1], 0)
            jobs = self._commit()
        if not jobs and options.done_exit:
            self.handle_command('A!')
            for sock in self._status:
                sock.write('!')
            os._exit(0)

    def handle_message(self, sock, message):
        with self._lock:
            done = False
            start = message.index('\\')
            jid = int(message[1:start])
            if jid < 0 or jid not in self._jobs or self._jobs[jid] != self._status[sock][0]:
                return
            self.output.write('< worker {}: {}\n'.format(sock.address, message))
            content = message[start + 1:]
            if message[0] == 'S':  # solved
                tid = self._status[sock][1]
                self._jobs[jid].tasks[tid].solved = True
                if content[0] == '1' or all([task.solved for task in self._jobs[jid].tasks]):  # SAT or all tasks solved
                    self._jobs[jid].add_history_item(('S', content))
                    self._jobs[jid]['status'] = 2
                    self._swap_jobs(jid, -1)
                else:
                    self._jobs[jid].add_history_item(('U', content, tid))
                    self._swap_jobs(jid, -1, tid)
                if not self._commit():
                    done = True
        if done and options.done_exit:
            self.handle_command('A!')
            os._exit(0)

    def handle_close(self, sock):
        with self._lock:
            self.output.write('- worker {}\n'.format(sock.address))
            jid = self._jobs.keys_of(self._status[sock][0])[0]
            if jid >= 0:
                self._jobs[jid].add_history_item(('-', 1, self._status[sock][1]))
            self._status.pop(sock)
            self._commit()

    def handle_command(self, message):
        with self._lock:
            if message[0] == 'S':
                message = message[1:]
                last = message[0] != '\\'
                if not last:
                    message = message[1:]
                start = message.index('\\')
                name = message[:start]
                code = message[start + 1:]
                jid = max(self._jobs.keys()) + 1
                for _jid in self._jobs:
                    if self._jobs[_jid]['name'] == name:
                        if self._jobs[_jid].get('status', -1) != -2:
                            self.output.write('$ JOB {} ALREADY CLOSED: {}\n'.format(jid, name))
                            return
                        jid = _jid
                        break
                if jid not in self._jobs:
                    self._jobs[jid] = Job(name, [Task(code)])
                else:
                    self._jobs[jid].tasks.append(Task(code))
                self._jobs[jid]['status'] = 0 if last else -2
                self._commit()
            elif message[0] == 'Q':
                jid = int(message[1:])
                self._jobs[jid]['status'] = -1
                workers = self._swap_jobs(jid, -1)  # from old JOB to IDLE
                self._commit()
            elif message[0] == 'D':
                try:
                    file = open(message[1:], 'wb')
                    pickle.dump(self._jobs, file)
                except:
                   self.output.write('$ DUMP ERROR: {}\n'.format(message))
                else:
                   file.close()
            elif message[0] == 'A':
                l = [str(sys.argv)]
                for jid in self._jobs:
                    if jid < 0:
                        continue
                    name = self._jobs[jid]['name']
                    result_code = int(self._jobs[jid].get('result', 0))
                    if result_code == 1:
                        result = 'sat'
                    elif result_code == -1:
                        result = 'unsat'
                    else:
                        result = 'unknown'
                    l.append('{} {} {:.2f}'.format(name, result, self._jobs[jid].get('elapsed', -1)))
                if message[1:].startswith('!'):
                    self.output.write('\nDONE:\n{}\n################################\n'.format(l[0]))
                    self.output.write('\n'.join(l[1:]))
                    self.output.write('\n')
                    self.output.flush()
                else:
                    with open(message[1:], 'w') as f:
                        f.write('\n'.join(l))
    def _commit(self):
        """
        Find job available (with POLICY) and then execute it
        """
        """POLICY: the first job that has one or more tasks without workers working on it
            is executed by all the workers idle/available
        jids = [jid for jid in self._jobs if jid >= 0 and self._jobs[jid]['status'] == 0]
        for jid in jids:
            commitments = self._get_commitments(jid, False)
            if not all(commitments.values()):
                self._swap_jobs(-1, jid)
                return
        """

        """POLICY: finds the first job with some workers working on it, or if none, the first unsolved"""
        jids = [jid for jid in self._jobs if jid >= 0 and self._jobs[jid]['status'] == 1]
        if not jids:
            jids = [jid for jid in self._jobs if jid >= 0 and self._jobs[jid]['status'] == 0]
        if jids:
            self._swap_jobs(-1, jids[0])
            return [jids[0]]
        else:
            return []

    def _swap_jobs(self, jid_prev, jid_next, filter=None):
        """
        frees workers on jid_prev (eventually only on task_id filter) and put them on jid_next with a POLICY
        """
        if jid_prev not in self._jobs or jid_next not in self._jobs:
            return []
        job_prev, job_next = self._jobs[jid_prev], self._jobs[jid_next]
        if filter is None:
            workers = [sock for socks in self._get_commitments(jid_prev).values() for sock in socks]
        else:
            workers = self._get_commitments(jid_prev)[filter]
        if workers:
            if jid_prev >= 0:
                job_prev.add_history_item(('-', len(workers)))
                self._multicast('Q{}'.format(jid_prev), to=workers)
            if jid_next >= 0:
                job_next['status'] = 1
                tid_workers = {tid: [] for tid in self._get_commitments(jid_next, False)}
                for sock in workers:
                    """ POLICY: every worker is assigned to the not solved task that have the minimum number
                        of workers still working on. that spreads the workers on all the tasks of the job
                    """
                    commitments = self._get_commitments(jid_next, False)
                    rev = {len(commitments[tid]): tid for tid in commitments}
                    tid = rev[min(rev)]
                    tid_workers[tid].append(sock)
                    self._status[sock] = (job_next, tid)
                for tid in tid_workers:
                    if tid_workers[tid]:
                        job_next.add_history_item(('+', len(tid_workers[tid]), tid))
                        self._multicast('S{}\\{}'.format(jid_next, job_next.tasks[tid].code), to=tid_workers[tid])
            else:
                for sock in workers:
                    self._status[sock] = (job_next, 0)
        return workers

    def _get_commitments(self, jid, filter=None):
        """
        gets the commitments (what task a worker is doing on a job) in a dictonary task_id -> [list of workers]
        if filter is set, the tasks in the return dict are the only with solved = filter
        """
        job = self._jobs[jid]
        commitments = {tid: [] for tid in range(len(job.tasks))}
        if filter is not None:
            commitments = {tid: commitments[tid] for tid in commitments if job.tasks[tid].solved == filter}
        for sock in self._status:
            if self._status[sock][0] == job:
                tid = self._status[sock][1]
                if tid in commitments:
                    commitments[tid].append(sock)
        return commitments

    def _multicast(self, message, to=None):
        """
        sends the message to all workers if <to> is None, else send only to <to> (list expected)
        """
        recipients = self._rlist if to is None else to
        for sock in recipients:
            if sock is self._socket:
                continue
            sock.write(message)

    def __repr__(self):
        workers = {sock.address: (self._jobs.keys_of(self._status[sock][0])[0], self._status[sock][1])
                   for sock in self._status}
        return '{}\n{}'.format(
            '\n'.join([str((jid, self._jobs[jid])) for jid in self._jobs]),
            '\n'.join([str(item) for item in workers.items()])
        )


class CommandServer(Server):
    def __init__(self, port, worker_server, opensmt):
        if not isinstance(worker_server, WorkerServer):
            raise TypeError
        self._worker_server = worker_server
        self._opensmt = opensmt
        super(CommandServer, self).__init__(port)

    def handle_message(self, sock, message):
        self.output.write('* {} size:{}\n'.format(sock.address, len(message)))
        if message[0] == '!':
            if len(message) > 1 and message[1] == 'S':
                if not options.opensmt:
                    self.output.write('* OPENSMT executable path not specified\n')
                    return
                start = message.index('\\')
                name = message[2:start]
                code = message[start + 1:]
                temp_fd, temp_name = tempfile.mkstemp('.smt2')
                dump_prefix = '/dev/shm/{}'.format(os.path.basename(temp_name))
                with open(options.file_options) as options_file:
                    smt_options = options_file.read().split('\n')
                smt_options.append('(set-option :split-num {})'.format(options.split_num))
                smt_options.append('(set-option :dump-state "{}")'.format(dump_prefix))
                with os.fdopen(temp_fd, 'w') as file:
                    file.write('{}\n{}'.format(
                        '\n'.join(smt_options),
                        code
                    ))
                start_time = time.time()
                subprocess.call([self._opensmt, temp_name], stdout=open('/dev/null', 'w'), stderr=subprocess.STDOUT)
                try:
                    tasks = subprocess.check_output('ls {}-*'.format(dump_prefix), shell=True,
                                                    stderr=open('/dev/null', 'w')).split('\n')
                except:
                    self.output.write('* DONE without split: {}\n'.format(name))
                else:
                    tasks = tasks[:-1]
                    for task in tasks:
                        with open(task, 'rb') as file:
                            self._worker_server.handle_command('S{}{}\\{}'.format(
                                '' if task is tasks[-1] else '\\',
                                name,
                                file.read()
                            ))
                        os.remove(task)
                finally:
                    self.output.write('T {} {}\n'.format(name, time.time() - start_time))
                    self.output.flush()
            else:
                self.output.write('{}\n'.format(self._worker_server))
            try:
                sock.write('D')
            except:
                pass
        else:
            self._worker_server.handle_command(message)



if __name__ == '__main__':
    parser = optparse.OptionParser()
    parser.add_option('-c', '--cport', dest='cport', type='int',
                      default=5000, help='specify commands port number')
    parser.add_option('-w', '--wport', dest='wport', type='int',
                      default=3000, help='specify workers port number')
    parser.add_option('-v', '--verbose', action='store_true', dest='verbose',
                      default=False, help='verbose output on stderr')
    parser.add_option('-t', '--timeout', dest='timeout', type='int',
                      default=None, help='timeout for each problem')
    parser.add_option('-o', '--opensmt', dest='opensmt', type='str',
                      default='../opensmt', help='opensmt executable')
    parser.add_option('-f', '--file-options', dest='file_options', type='str',
                      default=None, help='option file containig headers')
    parser.add_option('-s', '--split-num', dest='split_num', type='int',
                      default=2, help='number of splits')
    parser.add_option('-d', '--done-exit', action='store_true', dest='done_exit',
                        default=False, help='if true server dies when all jobs are done')

    (options, args) = parser.parse_args()

    wserver = WorkerServer(options.wport, options.timeout)
    cserver = CommandServer(options.cport, wserver, options.opensmt)

    wserver.output = sys.stdout
    cserver.output = sys.stdout

    t = threading.Thread(target=wserver.run_forever)
    t.start()

    # try:
    cserver.run_forever()
    #except:
    #   os._exit(0)
