noinst_LTLIBRARIES = liblogics.la
#noinst_PROGRAMS = testsimplify

AM_CPPFLAGS=$(config_includedirs)

liblogics_la_SOURCES = Logic.C LRALogic.C Theory.C LRATheory.C UFTheory.C Tterm.C

if ENABLE_LIBRARY
include_HEADERS = LRALogic.h Logic.h Theory.h Tterm.h
endif

#testsimplify_SOURCES = TestSimplify.C

#testsimplify_LDADD = liblogics.la ../pterms/libpterms.la ../symbols/libsymbols.la ../sorts/libsorts.la ../smtsolvers/libsmtsolvers.la
