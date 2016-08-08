#!/usr/bin/env python
# -*- coding: utf-8 -*-

import net
import sys
import pathlib
import readline

__author__ = 'Matteo Marescotti'


def send_file(address, path):
    file = open(path, 'r')
    socket = net.Socket()
    socket.connect(address)
    socket.write({
        'command': 'solve',
        'name': pathlib.Path(path).name
    }, file.read())


def terminal(address):
    socket = net.Socket()
    socket.connect(address)
    while True:
        try:
            line = input('{}:{}> '.format(*socket.remote_address))
        except (KeyboardInterrupt, EOFError):
            print()
            break
        socket.write({'eval': line.strip()}, '')
        header, message = socket.read()
        print(message.decode())


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print('Usage: {} [host=127.0.0.1:]<port> [file [...]]'.format(sys.argv[0]), file=sys.stderr)
        sys.exit(1)
    else:
        if ':' not in sys.argv[1]:
            sys.argv[1] = '127.0.0.1:' + sys.argv[1]
        components = sys.argv[1].split(':')
        address = (components[0], int(components[1]))

    if len(sys.argv) > 2:
        for path in sys.argv[2:]:
            try:
                send_file(address, path)
            except FileNotFoundError:
                print('File not found: {}'.format(path), file=sys.stderr)
            except ConnectionError:
                print('Connection error.', file=sys.stderr)
                sys.exit(1)
    else:
        terminal(address)
