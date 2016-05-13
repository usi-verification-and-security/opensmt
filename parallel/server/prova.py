# import server
import socket
import collections
import enum
import traceback
import logging

logging.basicConfig(level=logging.WARNING, format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
logger = logging.getLogger('server')


class A(object):
    def __init__(self, a):
        self.a = a


class B(object):
    def __init__(self, b):
        self.b = b


class C(A,B):
    def __init__(self, a):
        A.__init__(self, a)

c=C('E')
print(c.a)
print(c.b)