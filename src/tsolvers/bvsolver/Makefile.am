noinst_LTLIBRARIES = libbvsolver.la

AM_CPPFLAGS=$(config_includedirs)

libbvsolver_la_SOURCES = BVSolver.h BVSolver.C BitBlaster.h BitBlaster.C BVStore.C BVStore.h Bvector.h

if ENABLE_LIBRARY
include_HEADERS = BVSolver.h BitBlaster.h BVStore.h Bvector.h
endif
