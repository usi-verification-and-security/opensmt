#SUBDIRS = axdiffsolver bvsolver dlsolver emptysolver lrasolver ctsolver
SUBDIRS = lrasolver egraph bvsolver

noinst_LTLIBRARIES = libtsolvers.la

AM_CPPFLAGS=$(config_includedirs)

libtsolvers_la_SOURCES = THandler.C THandler.h Deductions.C Deductions.h TSolver.C TSolverHandler.C LRATHandler.C UFTHandler.C
#libtsolvers_la_SOURCES = TSolver.h THandler.C THandler.h
libtsolvers_la_LIBADD = lrasolver/liblrasolver.la egraph/libegraph.la

if ENABLE_LIBRARY
include_HEADERS = Deductions.h LRATHandler.h THandler.h TSolver.h TSolverHandler.h UFTHandler.h
endif

#libtsolvers_la_LIBADD = axdiffsolver/libaxdiffsolver.la \
#			bvsolver/libbvsolver.la \
#			dlsolver/libdlsolver.la \
#			lrasolver/liblrasolver.la \
#			ctsolver/libctsolver.la \
#			emptysolver/libemptysolver.la
