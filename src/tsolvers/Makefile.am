#SUBDIRS = axdiffsolver bvsolver dlsolver emptysolver lrasolver liasolver ctsolver
SUBDIRS = lrasolver liasolver egraph bvsolver

noinst_LTLIBRARIES = libtsolvers.la

AM_CPPFLAGS=$(config_includedirs)

libtsolvers_la_SOURCES = THandler.C THandler.h Deductions.C Deductions.h TSolver.C LASolver.C TSolverHandler.C LRATHandler.C LIATHandler.C UFTHandler.C UFLRATHandler.C CUFTHandler.C
#libtsolvers_la_SOURCES = TSolver.h THandler.C THandler.h LASolver.h
libtsolvers_la_LIBADD = lrasolver/liblrasolver.la liasolver/libliasolver.la egraph/libegraph.la bvsolver/libbvsolver.la

if ENABLE_LIBRARY
include_HEADERS = Deductions.h LRATHandler.h LIATHandler.h THandler.h TSolver.h LASolver.h TSolverHandler.h UFTHandler.h UFLRATHandler.h CUFTHandler.h
endif

#libtsolvers_la_LIBADD = axdiffsolver/libaxdiffsolver.la \
#			bvsolver/libbvsolver.la \
#			dlsolver/libdlsolver.la \
#			lrasolver/liblrasolver.la \
#			liasolver/libliasolver.la \
#			ctsolver/libctsolver.la \
#			emptysolver/libemptysolver.la
