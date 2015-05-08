#!/usr/bin/env python
# -*- coding: utf-8 -*-

import sserver
import sys
import optparse
import os.path

__author__ = 'Matteo Marescotti'

class Socket(sserver.Socket):
    def write(self, msg):
        super(Socket, self).write(msg)
        self.read()

if __name__ == '__main__':
    parser = optparse.OptionParser("usage: %prog <host> [options]")
    parser.add_option('-p', '--port', dest='port', type='int',
                      default=5000, help='specify commands port number')
    (options, args) = parser.parse_args()
    if len(args) == 0:
        parser.error("missing <host> argument")

    s = Socket()
    s.connect((args[0], options.port))

    if len(args) == 1:
        s.write(sys.stdin.read())
    else:
        for filename in args[1:]:
            if not os.path.exists(filename):
                sys.stderr.write("{}: file doesn't exists\n".format(filename))
                continue
            with open(filename, 'r') as f:
                print filename
                s.write('{}S{}\\{}'.format(
                    '!' if filename.endswith('.smt2') else '',
                    os.path.splitext(os.path.basename(filename))[0],
                    f.read())
                )

    s.close()
