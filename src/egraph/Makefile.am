noinst_LTLIBRARIES = libegraph.la
noinst_PROGRAMS = test

INCLUDES=$(config_includedirs)


libegraph_la_SOURCES = Enode.h Enode.C EnodeStore.h EnodeStore.C

test_SOURCES = test.C
test_LDADD = libegraph.la ../logics/liblogics.la ../pterms/libpterms.la ../smtsolvers/libsmtsolvers.la ../terms/libterms.la ../sorts/libsorts.la


# libegraph_la_SOURCES = EgraphSolver.C \
# 		       EgraphStore.C \
# 		       EgraphExplain.C \
# 		       EgraphDTC.C \
# 		       EgraphDebug.C \
# 		       Egraph.h \
# 		       Enode.C Enode.h \
# 		       SigTab.C SigTab.h \
# 		       UFInterpolator.C UFInterpolator.h
