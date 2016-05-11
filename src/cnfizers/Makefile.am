noinst_LTLIBRARIES = libcnfizers.la

AM_CPPFLAGS=$(config_includedirs)

libcnfizers_la_SOURCES = Cnfizer.C Cnfizer.h Tseitin.C Tseitin.h TermMapper.C TermMapper.h

if WANT_LIBRARY
include_HEADERS = Cnfizer.h TermMapper.h Tseitin.h
endif
