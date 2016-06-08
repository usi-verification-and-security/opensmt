import sys
import os
from setuptools import setup
from distutils.extension import Extension
from datetime import datetime


short_description="OpenSMT2 SMT-Solver Wrapper"
long_description=\
"""
==========================
Opensmt SMT-Solver Wrapper
==========================

Provides a basic wrapping around the OpenSMT2 SMT Solver.

OpenSMT2 is developed at Universita' della Svizzera italiana.
For more information see

  http://verify.inf.usi.ch/opensmt.

"""

if __name__ == '__main__':

    if len(sys.argv) < 2:
        print "Usage: %s <opensmt_install_dir> <setup_args>" % sys.argv[0]
        exit(1)

    OPENSMT_DIR = sys.argv[1]
    del sys.argv[1]

    opensmt_ext = Extension('_opensmt', ['src/PySMT/opensmt_python_wrap.c'],
                          include_dirs=[os.path.join(OPENSMT_DIR, "include/opensmt")],
                          library_dirs=[os.path.join(OPENSMT_DIR, "lib")],
                          libraries=['opensmt2c','gmp','gmpxx', 'z'],
                          language='c',
                        )

    setup(name='popensmt',
          version="0.1dev1",
          author='PySMT Team',
          author_email='info@pysmt.org',
          url='https://github.com/pysmt/popensmt/',
          license='BSD',
          description=short_description,
          long_description=long_description,
          ext_modules=[opensmt_ext],
          py_modules=['opensmt'],
          classifiers = [
            "Programming Language :: Python",
            "Programming Language :: Python :: 3",
            "Development Status :: 4 - Beta",
            "Intended Audience :: Developers",
            "Topic :: Software Development :: Libraries :: Python Modules",
          ],
    )
