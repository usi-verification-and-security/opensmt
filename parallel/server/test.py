import server
import framework
import net
import sqlite3
import random
import logging


def split(node, n, level):
    if level <= 0:
        return
    for i in range(n):
        node.add_child(framework.SMTFormula(node.formula.smt, node.formula.data))
    for children in node['children']:
        split(children, n, level - 1)


class Socket(net.Socket):
    i = 0

    def __init__(self):
        super().__init__()
        self.i = Socket.i
        Socket.i += 1
        self.status = False

    def write(self, header, payload):
        if header.get('command') == 'stop':
            self.status = False
        else:
            self.status = True
        print('<write to={} {} {}'.format(self.i, header, payload))
        pass

    @property
    def remote_address(self):
        return self.i


class Solver(Socket, server.Solver):
    i = 0

    def __init__(self, solver):
        server.Solver.__init__(self, solver, solver.data)
        self.i = Solver.i
        Solver.i += 1
        self.data = solver.data
        self.tree = solver.tree


logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(name)s - %(levelname)s - %(message)s')
logger = logging.getLogger('server')

conn = sqlite3.Connection('test.db')

s = server.ParallelizationServer(3000, conn=conn, logger=logger)
solvers = [Socket() for _ in range(10)]
for sock in solvers:
    s._rlist.add(sock)
    s.handle_accept(sock)
    s.handle_message(sock, {'solver': 'opensmt' + str(sock.i)}, '')

for solver in set(s._rlist):
    if isinstance(solver, server.Solver):
        s._rlist.remove(solver)
        s._rlist.add(Solver(solver))

c = Socket()
s.handle_message(c, {'command': 'solve', 'instance': 'i1'}, 'SMTDATA')
assert all([solver.tree is s._trees[0] for solver in s._rlist if isinstance(solver, Solver)])
split(s._trees[0].root, 2, 4)
s._trees[0].db_dump()
for solver in s._trees[0]._solvers:
    s._trees[0].assign_solvers(solver, s._trees[0].root['children'][0]['children'][0])

sock = sock1 = None
while True:
    sock, sock1 = random.sample(s._rlist, 2)
    if isinstance(sock, Solver) and isinstance(sock1, Solver):
        break

s._trees[0].assign_solvers(sock1, s._trees[0].root)

s.handle_message(sock, {'instance': s._trees[0].name,
                                       'hash': s._trees[0].node_hash(s._trees[0].solver_node(sock)),
                                       'status': 'sat'}, '')




# conn = sqlite3.Connection('test.db')
# m = server.SocketParallelizationTree('F1', 'F1', framework.SMTFormula('SMTDATA'), conn=conn)
# m.stop()
# split(m.root, 2, 4)
# m.start()
#
# m.db_dump()
# n = server.SocketParallelizationTree('F1', 'F1', framework.SMTFormula(), conn=conn)
# n.db_load()
# assert n.root['status'] == m.root['status']
# assert len(n.root['children']) == len(m.root['children'])
# assert len(n.root['children'][0]['children']) == len(m.root['children'][0]['children'])
#
# s = [Solver({'solver': 'opensmt'}) for _ in range(9)]
# m.assign_solvers(s[0])
# m.assign_solvers(s[1], m.root)
# m.assign_solvers(s[2], m.root)
# m.assign_solvers(s[4], m.root['children'][1]['children'][0])
# m.assign_solvers(s[8], m.root['children'][1]['children'][0]['children'][0]['children'][0])
# m.assign_solvers(s[6], m.root['children'][0]['children'][0]['children'][1]['children'][0])
# m.assign_solvers(s[7], m.root['children'][0]['children'][0]['children'][1]['children'][1])
# assert m.solver_node(s[2]) is m.root
# assert s[1] in m.root['solvers'] and s[2] in m.root['solvers']
# assert s[1] in m._solvers and s[2] in m._solvers
# m.assign_solvers(s[3], m.root['children'][0]['children'][0])
# assert m.solver_node(s[2]) is m.root
# m.assign_solvers(s[2], m.root['children'][0]['children'][0])
# assert s[2] not in m.root['solvers']
# assert s[2] in m.root['children'][0]['children'][0]['solvers'] and s[3] in m.root['children'][0]['children'][0][
#     'solvers']
# m.assign_solvers(s[3])
# assert s[3] not in m.root['children'][0]['children'][0]['solvers']
#
# assert len(m.root['children'][0]['children'][0]['solvers']) == 1
#
# # m.root['children'][0]['children'][0]['children'][0]['status'] = framework.SolveState.unsat
# m.handle_message(s[4], {'hash': m.node_hash(m.solver_node(s[4])), 'instance': 'F1', 'status': 'unsat'}, '')
# assert len(m.root['solvers']) == 1
# m.assign_solvers(s[5], m.root['children'][0]['children'][1])
# # m.root['children'][0]['children'][0]['children'][1]['status'] = framework.SolveState.sat
# m.handle_message(s[7], {'hash': m.node_hash(m.solver_node(s[7])), 'instance': 'F1', 'status': 'sat'}, '')
# assert len(m.root['children'][0]['children'][1]['solvers']) == 0
# assert len(m.root['solvers']) == 0
# assert all([False if isinstance(item, server.net.Socket) else True for item in m.reverse])
# assert m.root['status'] == framework.SolveState.sat
# assert all([not s.status for s in s])
# conn.close()
