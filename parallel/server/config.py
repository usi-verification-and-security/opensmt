import pathlib

port = 3000
portfolio_max = 0
partition_timeout = None
partition_policy = [2, 2]
solving_timeout = 1000

_benchmarks_path = pathlib.Path(__file__).parent / '../../test/std_benchmarks'
files = [str(i.resolve()) for i in _benchmarks_path.glob('*.smt2')]

# files = """../../test/std_benchmarks/NEQ_NEQ015_size6.smt2
# ../../test/std_benchmarks/NEQ_NEQ032_size3.smt2
# ../../test/std_benchmarks/QG-classification_loops6_gensys_icl093.smt2
# ../../test/std_benchmarks/QG-classification_qg5_dead_dnd046.smt2
# ../../test/std_benchmarks/QG-classification_qg5_gensys_icl1069.smt2""".split('\n')
