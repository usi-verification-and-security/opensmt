# !/usr/bin/env python
# -*- coding: utf-8 -*-

import enum
import sqlite3
import hashlib
import json

__author__ = 'Matteo Marescotti'


class Observer(object):
    # only variables of these types will be recorded in the reverse dict
    reverse_types = (str, int)

    class Type(type):
        pass

    """ this declaration is just for IDE type checking:
        when you declare a class child of Observer.ObservedBase IDE knows that there are these members below.
        Watched objects should not be declared directly:
            they should be passed to Observer._observed(cls) who replaces there members properly"""

    class ObservedBase(object):

        def observed(self, cls, *args, **kwargs):
            raise TypeError

        def paths(self):
            raise TypeError

        @property
        def observer(self):
            raise TypeError

    def __init__(self):
        self._reverse = {}
        self._observe = False
        self._root = None

    def stop(self):
        self._observe = False

    def start(self):
        self._observe = True
        self.update_reverse()

    @property
    def observing(self):
        return self._observe

    def update_reverse(self):
        if self.observing:
            self._reverse.clear()
            if isinstance(self.root, self.reverse_types):
                self._reverse[self.root] = [[]]
            for path, value in self._root.paths():
                if isinstance(value, self.reverse_types):
                    self._reverse.setdefault(value, []).append(path)

    def _observed_type(self, base):
        observer = self

        def observe(func):
            def wrapped(self, *args, **kwargs):
                before = self.copy()
                result = func(self, *args, **kwargs)
                after = self.copy()
                if before != after:
                    observer.update_reverse()
                return result

            return wrapped

        skip = ('__iter__', '__len__', '__getattribute__', '__contains__', 'copy', '__repr__', '__str__', '__getitem__')

        class ObservedMeta(type(observer).Type):
            def __new__(cls, name, bases, dct):
                for attr in dir(base):
                    if attr not in skip:
                        func = getattr(base, attr)
                        if isinstance(func, (type(list.append), type(list.__setitem__))):
                            dct[attr] = observe(func)
                return type.__new__(cls, name, bases, dct)

        class Observed(base, type(observer).ObservedBase, metaclass=ObservedMeta):
            def observed(self, cls, *args, **kwargs):
                return observer._observed_type(cls)(*args, **kwargs)

            def paths(self):
                if issubclass(base, dict):
                    items = self.items()
                elif issubclass(base, (list, set)):
                    items = enumerate(self)
                else:
                    raise TypeError

                for _, value in items:
                    yield [self], value
                    if issubclass(type(type(value)), type(observer).Type):
                        for path, subvalue in value.paths():
                            yield [self] + path, subvalue

            @property
            def observer(self):
                return observer

        return Observed

    def observed(self, cls, *args, **kwargs):
        return self._observed_type(cls)(*args, **kwargs)

    @property
    def reverse(self):
        return self._reverse

    @property
    def root(self):
        return self._root


class SolveState(enum.Enum):
    unknown = 0
    sat = 1
    unsat = -1


class SMTFormula(object):
    def __init__(self, smtlib):
        self.smtlib = smtlib

    def __str__(self):
        return self.smtlib

    def json_dump(self):
        return json.dumps({'smtlib': self.smtlib})

    @staticmethod
    def json_load(dump):
        d = json.loads(dump)
        return SMTFormula(d['smtlib'])


class Node(dict, Observer.ObservedBase):
    def __init__(self, formula=None):
        super().__init__()
        self.formula = formula
        self['children'] = self.observed(list)
        self['status'] = SolveState.unknown

    def __repr__(self):
        return '<{} {} state:{}>'.format(
            self.__class__.__bases__[0].__name__,
            self.observer.node_path(self, True),
            self['status'].name, self['children']
        )

    def __hash__(self):
        return id(self)

    def __cmp__(self, other):
        return id(self) == id(other)

    def __eq__(self, other):
        return id(self) == id(other)

    @staticmethod
    def db_setup(conn, table_prefix=''):
        cursor = conn.cursor()
        cursor.execute("CREATE TABLE IF NOT EXISTS {}Node ("
                       "instance TEXT NOT NULL, "
                       "nid INTEGER NOT NULL, "
                       "parent INTEGER NOT NULL, "
                       "state TEXT NOT NULL, "
                       "formula TEXT, "
                       "PRIMARY KEY (instance, nid)"
                       ");".format(table_prefix))
        conn.commit()

    def db_dump(self, conn, parent_index=0, table_prefix=''):
        if type(conn) is sqlite3.Connection:  # cursor initiated only once for all recursive calls
            cursor = conn.cursor()
        else:
            cursor = conn

        nid = cursor.execute("SELECT COALESCE(MAX(nid)+1,1) FROM {}Node WHERE instance=?;".format(table_prefix), (
            self.observer.name,
        )).fetchall()[0][0]
        cursor.execute("INSERT INTO {}Node VALUES (?,?,?,?,?);".format(table_prefix), (
            self.observer.name,
            nid,
            parent_index,
            self['status'].name,
            self.formula.json_dump()
        ))
        for i, child in enumerate(self['children']):
            child.db_dump(cursor, parent_index=nid, table_prefix=table_prefix)
        if type(conn) is sqlite3.Connection:
            conn.commit()

    def db_load(self, conn, nid=1, table_prefix=''):
        if type(conn) is sqlite3.Connection:  # cursor initiated only once for all recursive calls
            cursor = conn.cursor()
        else:
            cursor = conn

        try:
            row = cursor.execute("SELECT * FROM {}Node WHERE instance=? AND nid=?".format(table_prefix), (
                self.observer.name,
                nid
            )).fetchall()[0]
        except:
            raise ValueError('requested nid={} from DB not exists'.format(nid))
        self['status'] = SolveState.__members__[row[3]]
        self.formula = SMTFormula.json_load(row[4])

        for row in cursor.execute("SELECT nid FROM {}Node WHERE instance=? AND parent=?".format(table_prefix), (
                self.observer.name,
                nid
        )).fetchall():
            self.add_child().db_load(cursor, nid=row[0], table_prefix=table_prefix)

        if type(conn) is sqlite3.Connection:
            conn.commit()

    def add_child(self, *args, **kwargs):
        raise NotImplementedError


class AndNode(Node):
    def add_child(self, *args, **kwargs):
        child = self.observer.new_node(OrNode, *args, **kwargs)
        self['children'].append(child)
        return child


class OrNode(Node):
    def add_child(self, *args, **kwargs):
        child = self.observer.new_node(AndNode, *args, **kwargs)
        self['children'].append(child)
        return child


class ParallelizationTree(Observer):
    reverse_types = (Node,)

    def __init__(self, name, formula=None, conn=None, table_prefix=''):
        super().__init__()
        self._and_nodes = 1
        self._or_nodes = 0
        self._nodes = 1
        self.name = name
        self._conn = conn
        self._table_prefix = table_prefix
        self._root = self.new_node(AndNode, formula)
        self.start()
        if self._conn:
            self.root.db_setup(self._conn, table_prefix=self._table_prefix)

    def new_node(self, cls, *args, **kwargs):
        if issubclass(cls, AndNode):
            self._and_nodes += 1
        elif issubclass(cls, OrNode):
            self._or_nodes += 1
        else:
            raise TypeError
        self._nodes += 1
        return self.observed(cls, *args, **kwargs)

    def db_load(self):
        self.root.db_load(self._conn, table_prefix=self._table_prefix)

    def db_dump(self):
        self._conn.cursor().execute("DELETE FROM {}Node WHERE instance=?;".format(self._table_prefix), (
            self.name,
        ))
        self._conn.commit()
        self.root.db_dump(self._conn, table_prefix=self._table_prefix)

    def node_path(self, node, keys=False):
        if not isinstance(node, Node):
            raise TypeError
        if node not in self._reverse:
            raise ValueError
        path = self._reverse[node][0]
        if not keys:
            return [n for n in path if isinstance(n, Node)]
        path = list(path + [node])
        return [path[i].index(path[i + 1]) for i in range(1, len(path), 2)]

    def level(self, i=0):
        if i < 0:
            raise ValueError
        level = [self.root]
        while i > 0:
            i -= 1
            parents = level.copy()
            level.clear()
            for node in parents:
                level.extend(node['children'])
        return level

    def update_reverse(self):
        if not self.observing:
            return
        super().update_reverse()
        self._observe = False
        for path in self._reverse.setdefault(SolveState.sat, []) + self._reverse.setdefault(SolveState.unsat, []):
            path = [node for node in path if isinstance(node, Node)]
            state = path[-1]['status']  # sat or unsat of the leaf
            for i in range(1, len(path) + 1):  # from the last one until the first (root)
                node = path[-i]
                if node['status'] is state:  # already labeled
                    continue
                if isinstance(node, OrNode) and state is SolveState.unsat:
                    if all([node['status'] == state for node in node['children']]):
                        node['status'] = state
                    else:
                        break
                else:
                    node['status'] = state
            for node in path:
                if node['status'] is state:
                    self.prune(node)
                    break
        self._observe = True
        super().update_reverse()

    def prune(self, node):
        pass
