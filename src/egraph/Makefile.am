noinst_LTLIBRARIES = libegraph.la
noinst_PROGRAMS = test gctest test3

INCLUDES=$(config_includedirs)


libegraph_la_SOURCES = Enode.h Enode.C EnodeStore.h EnodeStore.C \
                       EgraphSolver.C EgraphDebug.C EgraphExplain.C


test_SOURCES = test.C
test_LDADD = libegraph.la ../logics/liblogics.la ../pterms/libpterms.la ../smtsolvers/libsmtsolvers.la ../symbols/libsymbols.la ../sorts/libsorts.la

test3_SOURCES = test3.C
test3_LDADD = libegraph.la ../logics/liblogics.la ../pterms/libpterms.la ../smtsolvers/libsmtsolvers.la ../symbols/libsymbols.la ../sorts/libsorts.la

gctest_SOURCES = GCTest.C GCTest.h
gctest_LDADD = libegraph.la ../logics/liblogics.la ../pterms/libpterms.la ../smtsolvers/libsmtsolvers.la ../symbols/libsymbols.la ../sorts/libsorts.la


# libegraph_la_SOURCES = EgraphSolver.C \
# 		       EgraphStore.C \
# 		       EgraphExplain.C \
# 		       EgraphDTC.C \
# 		       EgraphDebug.C \
# 		       Egraph.h \
# 		       Enode.C Enode.h \
# 		       SigTab.C SigTab.h \
# 		       UFInterpolator.C UFInterpolator.h
