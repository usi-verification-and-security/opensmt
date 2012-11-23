noinst_LTLIBRARIES = libcnfparser.la

BUILT_SOURCES = cnfparser.cc cnfparser.h

INCLUDES = $(config_includedirs)

AM_YFLAGS = -d --name-prefix=cnf
AM_LFLAGS = -olex.yy.c -Pcnf

libcnfparser_la_SOURCES = cnfparser.yy cnflexer.ll
