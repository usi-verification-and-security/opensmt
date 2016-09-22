noinst_LTLIBRARIES = libproof.la

AM_CPPFLAGS=$(config_includedirs)

if ENABLE_LIBRARY
include_HEADERS = PG.h
endif

libproof_la_SOURCES = PG.h \
		      PGBuild.C PGCheck.C PGHelp.C \
		      PGHeuristics.C PGInterAux.C \
		      PGInterCheck.C PGInterpolator.C \
		      PGMain.C PGPrint.C PGRules.C \
		      PGTransformationAlgorithms.C
