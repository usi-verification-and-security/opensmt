noinst_LTLIBRARIES = libsmtsolvers.la

AM_CPPFLAGS=$(config_includedirs)
libsmtsolvers_la_SOURCES = Proof.C Proof.h \
			   SimpSMTSolver.C SimpSMTSolver.h \
			   CoreSMTSolver.C CoreSMTSolver.h \
			   SMTSolver.h Debug.C Theory.C TheoryInterpolator.h

if WANT_LIBRARY
include_HEADERS = CoreSMTSolver.h Proof.h SMTSolver.h SimpSMTSolver.h TheoryInterpolator.h
endif

#libsmtsolvers_la_SOURCES = CoreSMTSolver.C CoreSMTSolver.h \
#			   SimpSMTSolver.C SimpSMTSolver.h \
#			   Proof.C Proof.h \
#			   Debug.C \
#			   Theory.C TheoryCombination.C \
#			   SMTConfig.C SMTConfig.h \
#			   SMTSolver.h
