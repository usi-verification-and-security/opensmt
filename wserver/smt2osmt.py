__author__ = 'matteo'

import sys
import os
import os.path
import subprocess
import tempfile

if len(sys.argv) < 3:
    sys.stdout.write("usage: {} OPENSMT SMT2 [SMT2 ...]\n")
    sys.exit(1)

devnull = open('/dev/null', 'w')

for filename in sys.argv[2:]:
    f = open(filename, 'r')
    s = f.read()
    f.close()
    try:
        s.index('(write-state')
    except ValueError:
        try:
            n = s.index('(check-sat)')
        except ValueError:
            sys.stderr.write("(check-sat) not found in {}\n".format(filename))
            continue
        osmt2filename = os.path.dirname(filename)+"/"+".".join(os.path.basename(filename).split('.')[:-1]) + '.osmt2'
        s = "{}{}\n(exit)\n".format(
            s[:n],
            '(write-state "{}")'.format(osmt2filename)
        )
        sys.stdout.write('{} -> {} ... '.format(filename, osmt2filename))
        sys.stdout.flush()
        fd, tempsmt = tempfile.mkstemp('.smt2')
        f = os.fdopen(fd, 'w')
        f.write(s)
        f.close()
        process = subprocess.Popen(
            [sys.argv[1], tempsmt],
            stdin=subprocess.PIPE,
            stdout=devnull,
            stderr=subprocess.STDOUT
        )
        process.communicate(s)
        sys.stdout.write('{}\n'.format(process.returncode))

devnull.close()