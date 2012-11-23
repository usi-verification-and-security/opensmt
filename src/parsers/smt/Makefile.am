noinst_LTLIBRARIES = libsmtparser.la

BUILT_SOURCES = smtparser.cc smtparser.h

INCLUDES = $(config_includedirs)

AM_YFLAGS = -d --name-prefix=smt
AM_LFLAGS = -olex.yy.c -Psmt

libsmtparser_la_SOURCES = smtparser.yy smtlexer.ll
