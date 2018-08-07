noinst_LTLIBRARIES = libpterms.la

AM_CPPFLAGS=$(config_includedirs)

libpterms_la_SOURCES = Pterm.h Pterm.C PtStore.h PtStore.C PTRef.h PTRef.C PtStructs.h PtStructs.C

if ENABLE_LIBRARY
include_HEADERS = PtStore.h Pterm.h PTRef.h PtStructs.h
endif
