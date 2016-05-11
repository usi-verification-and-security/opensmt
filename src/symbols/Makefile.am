noinst_LTLIBRARIES = libsymbols.la

AM_CPPFLAGS=$(config_includedirs)

libsymbols_la_SOURCES = Symbol.h SymStore.C SymStore.h

if WANT_LIBRARY
include_HEADERS = SymStore.h Symbol.h
endif
