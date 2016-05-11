noinst_LTLIBRARIES = liblrasolver.la

AM_CPPFLAGS=$(config_includedirs)

liblrasolver_la_SOURCES = LAVar.h LAVar.C Delta.h Delta.C LRASolver.h LRASolver.C LAArray.h LAArray.C LARow.h LARow.C LAColumn.h LAColumn.C

if WANT_LIBRARY
include_HEADERS = Delta.h LAArray.h LAColumn.h LARow.h LAVar.h LRASolver.h
endif
