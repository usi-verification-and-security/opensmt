import os
from setuptools import setup
from distutils.extension import Extension
from datetime import datetime

#YICES_VERSION="2.4.1"
#YICES_DIR= "yices-%s" % YICES_VERSION

#PYICES_MINOR_VERSION='%s' % datetime.utcnow().strftime("%y%m%d")
# Major number is Yices Version, minor number creation date of the bindings
#PYICES_VERSION='%s.%s' % (YICES_VERSION, PYICES_MINOR_VERSION)

OPENSMT_DIR = "/home/hyvaeria/opensmt-install/"
opensmt_ext = Extension('_opensmt', ['src/PySMT/opensmt_python_wrap.c'],
                      include_dirs=[os.path.join(OPENSMT_DIR, "include/opensmt")],
                      library_dirs=[os.path.join(OPENSMT_DIR, "lib")],
                      libraries=['opensmt2c','gmp','gmpxx', 'z'],
#                      libraries=['opensmt2c'],
                      language='c',
                    )

short_description="OpenSMT2 SMT-Solver Wrapper"
long_description=\
"""
==========================
Opensmt SMT-Solver Wrapper
==========================

Provides a basic wrapping around the OpenSMT2 SMT Solver.

OpenSMT2 is developed by USI, for more information:

  http://verify.inf.usi.ch/opensmt.

"""

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
