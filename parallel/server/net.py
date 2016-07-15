# !/usr/bin/env python
# -*- coding: utf-8 -*-

import socket
import select
import struct
import logging
import traceback
import time

__author__ = 'Matteo Marescotti'


class Socket(object):
    def __init__(self, sock=None):
        if sock is None:
            self._sock = socket.socket()
            self._sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        else:
            self._sock = sock

    def __repr__(self):
        return '<Socket fd={} local={} remote={}>'.format(self.fileno(), self.local_address, self.remote_address)

    @staticmethod
    def _bytes(item):
        if type(item) not in (str, bytes):
            item = str(item)
        if type(item) is str:
            item = item.encode('utf8')
        if type(item) is not bytes:
            raise TypeError
        return item

    def connect(self, address):
        self._sock.connect(address)

    def listen(self, address, backlog=250):
        self._sock.bind(address)
        self._sock.listen(backlog)

    def accept(self):
        sock, _ = self._sock.accept()
        return self.__class__(sock=sock)

    def read(self):
        content = b''
        length = self._sock.recv(4)
        if len(length) == 4:
            length = struct.unpack('!I', length)[0]
            while len(content) < length:
                buffer = self._sock.recv(length - len(content))
                if len(buffer) == 0:
                    raise ConnectionAbortedError
                content += buffer
        else:
            raise ConnectionAbortedError
        header = {}
        i = 0
        while content[i:i + 1] != b'\x00':
            pair = []
            for _ in range(2):
                length = struct.unpack('!B', content[i:i + 1])[0]
                i += 1
                pair.append(content[i:i + length])
                i += length
            header[pair[0].decode()] = pair[1].decode()
        i += 1
        return header, content[i:]

    def write(self, header, payload):
        dump = b''
        for key, value in header.items():
            key, value = map(self._bytes, (key, value))
            if len(key) == 0:
                raise ValueError('empty key is not allowed')
            dump += struct.pack('!B', len(key)) + key
            dump += struct.pack('!B', len(value)) + value
        dump += b'\x00'
        payload = self._bytes(payload)
        dump += payload
        length = len(dump)
        if length >= 2 ** 32:
            raise ValueError
        self._sock.send(struct.pack('!I', length))
        self._sock.send(dump)

    def close(self):
        self._sock.close()
        self._sock = None

    def fileno(self):
        return self._sock.fileno()

    @property
    def local_address(self):
        try:
            return self._sock.getsockname()
        except:
            pass

    @property
    def remote_address(self):
        try:
            return self._sock.getpeername()
        except:
            pass

    @property
    def endpoints(self):
        return self.local_address, self.remote_address


class Server(object):
    def __init__(self, port=None, timeout=None, logger=None):
        self._rlist = set()
        if port:
            self._sock = Socket()
            self._sock.listen(('0.0.0.0', port))
            self._rlist.add(self._sock)
        self._timeout = None if timeout is None else float(timeout)
        self._logger = logging.getLogger() if logger is None else logger

    def handle_accept(self, sock):
        pass

    def handle_message(self, sock, header, message):
        pass

    def handle_close(self, sock):
        pass

    def handle_timeout(self):
        pass

    def run_until_timeout(self, timeout=None):
        timeout_time = None
        if timeout is None:
            timeout = self._timeout
        try:
            rlist = select.select(self._rlist, [], [], timeout)[0]
            if len(rlist) == 0 or timeout == 0:
                timeout_time = time.time()
                self.handle_timeout()
            for sock in rlist:
                if sock is self._sock:
                    new_socket = self._sock.accept()
                    self._rlist.add(new_socket)
                    self.handle_accept(new_socket)
                    continue
                try:
                    header, message = sock.read()
                except ConnectionAbortedError:
                    self.handle_close(sock)
                    sock.close()
                    self._rlist.remove(sock)
                else:
                    self.handle_message(sock, header, message)
        except KeyboardInterrupt:
            raise
        except BaseException as exp:
            self.log(logging.ERROR, '{}\n{}'.format(
                type(exp).__name__,
                '\n'.join(('   {}'.format(line) for line in traceback.format_exc().split('\n')))
            ))
        return timeout_time

    def run_forever(self):
        last = time.time()
        while True:
            lts = self.run_until_timeout(max(0, self._timeout - (time.time() - last)))
            if lts:
                last = lts

    def close(self):
        self._sock.close()

    def log(self, level, message):
        self._logger.log(level, message)

    @property
    def address(self):
        return self._sock.local_address
