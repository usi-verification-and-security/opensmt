
BUILT_SOURCES = smt2newparser.h

INCLUDES = $(config_includedirs)

AM_YFLAGS = -d --name-prefix=smt2new
AM_LFLAGS = -olex.yy.c -Psmt2new

#bin_PROGRAMS = parsetest

#parsetest_SOURCES = parsetest.cc smt2newcontext.cc

LDADD = libsmt2newparser.la

noinst_LTLIBRARIES = libsmt2newparser.la

libsmt2newparser_la_SOURCES = smt2newparser.yy smt2newlexer.ll smt2newcontext.cc

