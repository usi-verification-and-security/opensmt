noinst_LTLIBRARIES = libsimplifiers.la

AM_CPPFLAGS=$(config_includedirs)

libsimplifiers_la_SOURCES = LA.C LA.h

if WANT_LIBRARY
include_HEADERS = LA.h
endif

#libsimplifiers_la_SOURCES = TopLevelProp.h TopLevelProp.C \
#			    ExpandITEs.h ExpandITEs.C \
#			    BVBooleanize.h BVBooleanize.C \
#			    DLRescale.h DLRescale.C \
#			    BVNormalize.h BVNormalize.C \
#			    Ackermanize.h Ackermanize.C \
#			    ArraySimplify.h ArraySimplify.C \
#			    Purify.C Purify.h \
#			    AXDiffPreproc.C AXDiffPreproc.h \
#			    AXDiffPreproc2.C AXDiffPreproc2.h
