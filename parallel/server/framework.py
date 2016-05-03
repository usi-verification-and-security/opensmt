# !/usr/bin/env python
# -*- coding: utf-8 -*-

import enum
import os
import pprint
import net


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

    def __init__(self, cls, *args, **kwargs):
        self._reverse = {}
        self._observe = False
        self._root = self._observed_type(cls)(*args, **kwargs)
        self.start()
        self.update_reverse()

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
                    if issubclass(type(type(value)), type(observer).Type):
                        for path, subvalue in value.paths():
                            yield [self] + path, subvalue
                    else:
                        yield [self], value

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
    def __init__(self, id, smt):
        self.smt = smt
        self.id = id

    def __str__(self):
        return str(self.id)


class Node(dict):
    def __repr__(self):
        return '<{} state:{}>'.format(self.__class__.__bases__[0].__name__, self['state'].name, self['children'])

    def __hash__(self):
        return id(self)

    def __cmp__(self, other):
        return id(self) == id(other)

    def __eq__(self, other):
        return id(self) == id(other)


class AndNode(Node, Observer.ObservedBase):
    def __init__(self, formula):
        super().__init__()
        self.formula = formula
        self['children'] = self.observed(list)
        self['state'] = SolveState.unknown

    def add_child(self, *args, **kwargs):
        self.observer.or_nodes += 1
        self['children'].append(self.observed(OrNode, *args, **kwargs))


class OrNode(Node, Observer.ObservedBase):
    def __init__(self, formula):
        super().__init__()
        self.formula = formula
        self['children'] = self.observed(list)
        self['state'] = SolveState.unknown

    def add_child(self, *args, **kwargs):
        self.observer.and_nodes += 1
        self['children'].append(self.observed(AndNode, *args, **kwargs))


class ParallelizationTree(Observer):
    reverse_types = (SolveState,)

    def __init__(self, formula):
        self.and_nodes = 0
        self.or_nodes = 0
        super().__init__(AndNode, formula)

    def update_reverse(self):
        if not self.observing:
            return
        super().update_reverse()
        self._observe = False
        for path in self._reverse.setdefault(SolveState.sat, []) + self._reverse.setdefault(SolveState.unsat, []):
            path = [node for node in path if isinstance(node, Node)]
            state = path[-1]['state']  # sat or unsat of the leaf
            for i in range(1, len(path) + 1):  # from the last one until the first (root)
                node = path[-i]
                if node['state'] is state:  # already labeled
                    continue
                if isinstance(node, OrNode) and state is SolveState.unsat:
                    if all([node['state'] == state for node in node['children']]):
                        print(node['children'])
                        node['state'] = state
                    else:
                        break
                else:
                    node['state'] = state
            for node in path:
                if node['state'] is state:
                    self.prune(node)
                    break
        self._observe = True
        super().update_reverse()

    def prune(self, path):
        pass
