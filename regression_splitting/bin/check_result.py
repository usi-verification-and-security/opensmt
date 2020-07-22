#!/usr/bin/env python3

import sys
import re

def die(s):
    print("Error in the split tree")
    print(s)
    sys.exit(1)

def getLinesFromOutput(file):
    lines = map(lambda x: x.strip(), open(file).readlines())
    lines = filter(lambda x: re.search("; [-]?[0-9][0-9]*", x), lines)
    lines = map(lambda x: x.split(), map(lambda x: x[2:], lines))
    lines = [list(map(lambda x: int(x), l)) for l in lines]
    for line in lines:
        abses = set(map(abs, line))
        if len(abses) != len(line):
            die("inconsistent path")
        if len(set(line)) != len(line):
            die("duplicates in a path")

    return lines

def getTree(lines):
    root = [{}, 0, 0]
    max_depth = -1
    for path in lines:
        max_depth = max(max_depth, len(path))

        curr = root
        for i in range(0, len(path)):
            lit = path[i]
            curr[2] += 1

            if lit not in curr[0]:
                curr[0][lit] = [{}, lit, 0]

            curr = curr[0][lit]
    return root, max_depth

def checkNode(node, depth, max_depth):
    if not (len(node[0]) == 2 or len(node[0]) == 0):
        die("Not a binary tree")

    children = list(node[0])
    if len(children) == 2:
        if children[0] != -children[1]:
            die("Children are not mutually exclusive")

    if (depth != max_depth) and (node[2] == 0):
        die("Not a balanced tree")

    if (max_depth > depth):
        if (node[2] != 2**(max_depth-depth)):
            die("Incorrect descendant count on node %s" % node)
    else:
        if (node[2] != 0):
            die("Incorrect descendant count on node %s" % node)

def checkTree(root, max_depth):
    queue = [[root, 0]]
    while len(queue) != 0:
        (node, depth) = queue.pop()
        checkNode(node, depth, max_depth)
        for key in node[0]:
            queue.append((node[0][key], depth+1))

if __name__ == '__main__':
    if len(sys.argv) != 3:
        print("Usage: %s <output-file> <expected>" % sys.argv[0])
        sys.exit(1)

    lines = getLinesFromOutput(sys.argv[1])
    expected = sys.argv[2]

    if len(lines) == 0 and expected == 'unknown':
        die("Expected a split")
        sys.exit(1)
    if len(lines) != 0 and expected != 'unknown':
        die("Expected %s but got splits" % expected)

    if expected != 'unknown':
        s = open(sys.argv[1]).read()
        mo = re.search('^(sat|unsat)', s)
        if not mo:
            die("Expected %s but found no result" % expected)
        if mo.group(1) != expected:
            die("Expected %s but got %s" % (expected, mo.group(1)))
        sys.exit(0)

    root, max_depth = getTree(lines)

    checkTree(root, max_depth)

    sys.exit(0)
