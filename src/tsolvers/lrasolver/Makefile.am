noinst_LTLIBRARIES = liblrasolver.la

AM_CPPFLAGS=$(config_includedirs)

liblrasolver_la_SOURCES = LAVar.h LAVar.C Delta.h Delta.C LRASolver.h LRASolver.C Polynomials.h LABounds.h LABounds.C BindedRows.h LARefs.h

if ENABLE_LIBRARY
include_HEADERS = Delta.h LAVar.h LRASolver.h Polynomials.h LABounds.h BindedRows.h LARefs.h
endif
