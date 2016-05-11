#SUBDIRS = parsers tsolvers smtsolvers api sorts logics symbols pterms egraph cnfizers simplifiers
SUBDIRS = parsers tsolvers smtsolvers api sorts logics symbols pterms cnfizers simplifiers symmetry common options

noinst_LTLIBRARIES = libopensmt.la

if WANT_LIBRARY
lib_LTLIBRARIES = libopensmt2.la
include_HEADERS = minisat/core/Solver.h minisat/core/SolverTypes.h minisat/mtl/Alg.h minisat/mtl/Heap.h minisat/mtl/Map.h minisat/mtl/Queue.h minisat/mtl/Sort.h minisat/mtl/Vec.h minisat/simp/SimpSolver.h opensmt2.h
endif

libopensmt_la_SOURCES =
libopensmt_la_LIBADD = parsers/libparsers.la \
		       tsolvers/libtsolvers.la \
		       smtsolvers/libsmtsolvers.la \
		       sorts/libsorts.la \
		       simplifiers/libsimplifiers.la \
		       api/libapi.la \
		       logics/liblogics.la \
		       symbols/libsymbols.la \
		       pterms/libpterms.la \
		       cnfizers/libcnfizers.la \
		       common/libcommon.la \
		       options/liboptions.la


libopensmt2_la_SOURCES = 
libopensmt2_la_LIBADD = parsers/libparsers.la \
		        tsolvers/libtsolvers.la \
		        smtsolvers/libsmtsolvers.la \
		        sorts/libsorts.la \
		        simplifiers/libsimplifiers.la \
		        api/libapi.la \
		        logics/liblogics.la \
		        symbols/libsymbols.la \
		        pterms/libpterms.la \
		        cnfizers/libcnfizers.la \
		        common/libcommon.la \
		        options/liboptions.la

