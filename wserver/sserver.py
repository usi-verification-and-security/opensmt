#!/usr/bin/env python
# -*- coding: utf-8 -*-

import socket
import optparse
import select
import struct
import threading
import sys
import time
import os
import pickle

__author__ = 'Matteo Marescotti'


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

    def close_client(self, sock):
        self.handle_close(sock)
        sock.close()
        self._rlist.remove(sock)

    def run_forever(self):
        while True:
            rlist = select.select(self._rlist, [], [], 10)[0]
            if len(rlist) == 0:
                self.handle_timeout()
                continue
            for sock in rlist:
                if sock is self._socket:
                    new_socket = self._socket.accept()
                    self._rlist.append(new_socket)
                    self.handle_accept(new_socket)
                    continue
                message = sock.read()
                length = len(message)
                if length == 0:
                    self.close_client(sock)
                    continue
                self.handle_message(sock, message)


class Job(dict):
    def __init__(self, name, **kwargs):
        self.update({
            'name': name,
            'status': 0,
            'history': [('CREATED', time.time())]
        })
        self.started = False
        super(Job, self).__init__(kwargs)

    def add_history_item(self, item):
        now = time.time()
        if item[0] == '+' and not self.started:
            self.started = now
        if item[0] == 'SOLVED':
            self.update({'elapsed': now - self.started})
        self.get('history').append((now, item))

    def safe_dump(self):
        return {key: self.get(key) for key in self if not key.startswith('_')}

    def __str__(self):
        return '{}'.format(self.safe_dump())


class WorkerServer(Server):
    _lock = threading.Lock()
    _status = {}
    _jobs = {
        -2: Job('!ERROR'),
        -1: Job('!IDLE')
    }

    def __init__(self, port, timeout):
        self._timeout = timeout
        super(WorkerServer, self).__init__(port)

    def handle_timeout(self):
        with self._lock:
            if not self._timeout:
                return
            min = time.time() - self._timeout
            for sock in self._status:
                job = self._status[sock]
                jid = [jid for jid in self._jobs if self._jobs[jid] == job][0]
                if job.started and job.started < min:
                    self.handle_command('Q{}'.format(jid))

    def handle_accept(self, sock):
        with self._lock:
            self.output.write('+ worker {}\n'.format(sock.address))
            self._status[sock] = self._jobs[-1]
            self._commit()

    def handle_message(self, sock, message):
        with self._lock:
            start = message.index('\\')
            jid = int(message[1:start])
            if jid < 0 or jid not in self._jobs or self._jobs[jid] != self._status[sock]:
                return
            self.output.write('< worker {}: {}\n'.format(sock.address, message))
            content = message[start + 1:]
            if message[0] == 'S':  # solved
                self._jobs[jid].add_history_item(('SOLVED', content))
                self._jobs[jid]['status'] = 1
                self._swap_jobs(jid, -1)
                self._commit()

    def handle_close(self, sock):
        with self._lock:
            self.output.write('- worker {}\n'.format(sock.address))
            jid = self._jobs.keys()[self._jobs.values().index(self._status[sock])]
            if jid >= 0:
                self._jobs[jid].add_history_item(('-', 1))
            self._status.pop(sock)
            self._commit()

    def handle_command(self, message):
        with self._lock:
            if message[0] == 'S':
                jid = max(self._jobs.keys()) + 1
                start = message.index('\\')
                self._jobs[jid] = Job(message[1:start], _code=message[start + 1:])
                self._commit()
            elif message[0] == 'Q':
                jid = int(message[1:])
                self._jobs[jid]['status'] = -1
                workers = self._swap_jobs(jid, -1)  # from old JOB to IDLE
                self._commit()
            elif message[0] == 'D':
                try:
                    pickle.dump({key: self._jobs[key].safe_dump() for key in self._jobs}, open(message[1:], 'wb'))
                except:
                    self.output.write('DUMP ERROR: {}'.format(message))

    def _commit(self):
        """
        Find a job not yet solved then send it to idle workers
        """
        jids = [jid for jid in self._jobs if jid >= 0 and self._jobs[jid]['status'] == 0]
        if jids:
            self._swap_jobs(-1, jids[0])

    def _swap_jobs(self, jid_prev, jid_next):
        """
        frees workers on jid_prev and put them on jid_next
        """
        if jid_prev not in self._jobs or jid_next not in self._jobs:
            return
        workers = []
        for sock in self._status:
            if self._status[sock] == self._jobs[jid_prev]:
                workers.append(sock)
                self._status[sock] = self._jobs[jid_next]
        if workers:
            if jid_prev >= 0:
                self._jobs[jid_prev].add_history_item(('-', len(workers)))
                self._broadcast('Q{}'.format(jid_prev), to=workers)
            if jid_next >= 0:
                self._jobs[jid_next].add_history_item(('+', len(workers)))
                self._broadcast('S{}\\{}'.format(jid_next, self._jobs[jid_next]['_code']), to=workers)
        return workers

    def _broadcast(self, message, to=None):
        """
        sends the message to all workers if <to> is None, else send only to <to> (list expected)
        """
        recipients = self._rlist if to is None else to
        for sock in recipients:
            if sock is self._socket:
                continue
            sock.write(message)

    def __str__(self):
        workers = {sock.address: self._jobs.keys()[self._jobs.values().index(self._status[sock])]
                   for sock in self._status}
        return '{}\n{}'.format(
            '\n'.join([str((key, self._jobs[key].safe_dump())) for key in self._jobs]),
            '\n'.join([str(item) for item in workers.items()])
        )


class CommandServer(Server):
    def __init__(self, port, worker_server):
        if not isinstance(worker_server, WorkerServer):
            raise TypeError
        self._worker_server = worker_server
        super(CommandServer, self).__init__(port)

    def handle_message(self, sock, message):
        self.output.write('* {} size:{}\n'.format(sock.address, len(message)))
        if message[0] == '!':
            self.output.write('{}\n'.format(self._worker_server))
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
    (options, args) = parser.parse_args()

    wserver = WorkerServer(options.wport, options.timeout)
    cserver = CommandServer(options.cport, wserver)

    wserver.output = sys.stderr
    cserver.output = sys.stderr

    t = threading.Thread(target=wserver.run_forever)
    t.start()

    #try:
    cserver.run_forever()
    #except:
     #   os._exit(0)