noinst_LTLIBRARIES = libapi.la

AM_CPPFLAGS=$(config_includedirs) -I../parsers/smt2new/

libapi_la_SOURCES = Interpret.C MainSolver.h MainSolver.C

libapi_la_LIBADD = -lreadline

if WANT_LIBRARY
include_HEADERS = MainSolver.h
endif

#libapi_la_SOURCES = opensmt_c.h opensmt_c.C Interpret.C
#libapi_la_SOURCES = opensmt_c.h opensmt_c.C OpenSMTContext.h OpenSMTContext.C Interpret.C
