noinst_LTLIBRARIES = liblogics.la
#noinst_PROGRAMS = testsimplify

AM_CPPFLAGS=$(config_includedirs)

liblogics_la_SOURCES = Logic.C LRALogic.C Theory.C LRATheory.C UFTheory.C UFLRATheory.C Tterm.C CUFLogic.C CUFTheory.C BVLogic.C

if ENABLE_LIBRARY
include_HEADERS = LRALogic.h Logic.h Theory.h UFLRATheory.h Tterm.h CUFLogic.h BVLogic.h
endif

#testsimplify_SOURCES = TestSimplify.C

#testsimplify_LDADD = liblogics.la ../pterms/libpterms.la ../symbols/libsymbols.la ../sorts/libsorts.la ../smtsolvers/libsmtsolvers.la
