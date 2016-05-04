import server
import framework
import net
import sqlite3


def split(node, n, level):
    if level <= 0:
        return
    for i in range(n):
        node.add_child(framework.SMTFormula(node.formula.id, node.formula.smt, node.formula.data))
    for children in node['children']:
        split(children, n, level - 1)


class Socket(net.Socket):
    i = 0

    def __init__(self):
        self.i = Socket.i
        Socket.i += 1

    def write(self, header, payload):
        # print('<write to={} {} {}'.format(self.i, header, payload))
        pass


conn = sqlite3.Connection('test.db')
m = server.SocketParallelizationTree(framework.SMTFormula('F1', 'SMTDATA'), conn=conn)
# m.root['a'] = 'b'
m.stop()
split(m.root, 2, 4)
m.start()
s = [Socket() for _ in range(8)]
m.assign_socket(s[0])
m.assign_socket(s[1], m.root)
m.assign_socket(s[2], m.root)
m.assign_socket(s[4], m.root['children'][1]['children'][0])
m.assign_socket(s[6], m.root['children'][0]['children'][0]['children'][1]['children'][0])
m.assign_socket(s[7], m.root['children'][0]['children'][0]['children'][1]['children'][1])
assert m.socket_node(s[2]) is m.root
assert s[1] in m.root['solvers'] and s[2] in m.root['solvers']
assert s[1] in m._sockets and s[2] in m._sockets
m.assign_socket(s[3], m.root['children'][0]['children'][0])
m.assign_socket(s[2], m.root['children'][0]['children'][0])
assert s[2] not in m.root['solvers']
assert s[2] in m.root['children'][0]['children'][0]['solvers'] and s[3] in m.root['children'][0]['children'][0][
    'solvers']
m.assign_socket(s[3])
assert s[3] not in m.root['children'][0]['children'][0]['solvers']

assert len(m.root['children'][0]['children'][0]['solvers']) == 1

# m.root['children'][0]['children'][0]['children'][0]['status'] = framework.SolveState.unsat
m.socket_message(s[6], {'id': 'F1', 'status': 'unsat'}, '')
assert len(m.root['solvers']) == 1
m.assign_socket(s[5], m.root['children'][0]['children'][1])
# m.root['children'][0]['children'][0]['children'][1]['status'] = framework.SolveState.sat
m.socket_message(s[7], {'id': 'F1', 'status': 'sat'}, '')
assert len(m.root['children'][0]['children'][1]['solvers']) == 0
assert len(m.root['solvers']) == 0
assert all([False if isinstance(item, server.net.Socket) else True for item in m.reverse])
assert m.root['status'] == framework.SolveState.sat

m.db_dump(conn)
n = server.SocketParallelizationTree(framework.SMTFormula('F1'), conn=conn)
n.db_load(conn)
assert n.root['status'] == m.root['status']
assert len(n.root['children']) == len(m.root['children'])
assert len(n.root['children'][0]['children']) == len(m.root['children'][0]['children'])
conn.close()
