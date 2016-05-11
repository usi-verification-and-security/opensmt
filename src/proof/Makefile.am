noinst_LTLIBRARIES = libproof.la

AM_CPPFLAGS=$(config_includedirs)

if WANT_LIBRARY
include_HEADERS = ProofGlobal.h ProofGraph.h
endif

libproof_la_SOURCES = ProofGlobal.h \
		      ProofGraphBuild.C ProofGraph.h \
		      ProofGraphHelp.C ProofGraphCheck.C ProofGraphMain.C \
		      ProofInterpolator.C
