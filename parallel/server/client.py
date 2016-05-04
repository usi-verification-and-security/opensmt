#!/usr/bin/env python
# -*- coding: utf-8 -*-

import net
import sys
import readline

if __name__ == '__main__':
    if len(sys.argv) < 2 or len(sys.argv) > 3:
        print('Usage: {} [host=127.0.0.1] <port>'.format(sys.argv[0]))
        sys.exit(1)
    elif len(sys.argv) == 2:
        address = ('127.0.0.1', int(sys.argv[1]))
    else:
        address = (sys.argv[1], int(sys.argv[2]))

    socket = net.Socket()
    try:
        socket.connect(address)
    except BaseException as e:
        print('Connection error: {}'.format(e))
        sys.exit(1)

    while True:
        try:
            line = input('{}:{}> '.format(*socket.remote_address))
        except (KeyboardInterrupt, EOFError):
            print()
            break
        if line.strip():
            socket.write({'eval': line.strip()}, '')
            header, message = socket.read()
            print(message.decode())
