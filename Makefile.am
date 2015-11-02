ACLOCAL_AMFLAGS = -I m4
AUTOMAKE_OPTIONS = subdir-objects

SUBDIRS = src

bin_PROGRAMS = opensmt

#noinst_PROGRAMS = testsimplify testegraph1 testegraph3 testegraph4 testegraph5 gctest

opensmt_SOURCES = src/bin/opensmt.C
opensmt_LDFLAGS =
# -lgmpxx -lgmp

#testsimplify_SOURCES = src/logics/TestSimplify.C
#testegraph1_SOURCES = src/tsolvers/egraph/test.C
#testegraph3_SOURCES = src/tsolvers/egraph/test3.C
#testegraph4_SOURCES = src/tsolvers/egraph/test4.C
#testegraph5_SOURCES = src/tsolvers/egraph/test5.C
#gctest_SOURCES = src/tsolvers/egraph/GCTest.C GCTest.h

LDADD = src/libopensmt.la -lgmpxx -lgmp
