import server
import framework
import net
import sqlite3
import random
import logging
import time
import sys
import select

solvers = [net.Socket() for i in range(100)]
for solver in solvers:
    solver.connect(('127.0.0.1', 3000))
    solver.write({'solver': 'dumb', 'version': 0}, '')

user = net.Socket()
user.connect(('127.0.0.1', 3000))
user.write({'command': 'solve', 'instance': 'i1'}, 'SMT')
todo = []

while True:
    while todo:
        todo.pop()()
    rlist = select.select(solvers, [], [])[0]
    for sock in rlist:
        header, message = sock.read()
        print()
        print('=== from ', sock.local_address[1], ' ===')
        print(header)
        print(message)
        print()
        if header['command'] == 'solve':
            if random.randint(0, 100) < 10:
                print('SOLVED!')
                todo.append(
                    lambda: sock.write({'instance': header['instance'], 'hash': header['hash'], 'status': 'sat'},
                                       ''))

        if header['command'] == 'partitions':
            print('partitions...')
            p = {'partitions': header['partitions'], 'instance': header['instance'], 'hash': header['hash']}
            message = ''
            for i in range(int(header['partitions'])):
                message += header['instance'] + '.' + str(i)
                p[i] = len(message)
            todo.append(lambda: sock.write(p, message))
        print()
