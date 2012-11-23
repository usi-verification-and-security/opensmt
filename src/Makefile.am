SUBDIRS = parsers smtsolvers common api sorts logics terms

noinst_LTLIBRARIES = libopensmt.la

if WANT_LIBRARY
lib_LTLIBRARIES = libopensmt-1.0.la
endif

libopensmt_la_SOURCES =
libopensmt_la_LIBADD = parsers/libparsers.la \
		       smtsolvers/libsmtsolvers.la \
		       common/libcommon.la \
		       sorts/libsorts.la \
		       api/libapi.la \
		       logics/liblogics.la \
		       terms/libterms.la

libopensmt_1_0_la_SOURCES = 
libopensmt_1_0_la_LIBADD = smtsolvers/libsmtsolvers.la \
		       common/libcommon.la \
		       sorts/libsorts.la \
		       api/libapi.la \
		       logics/liblogics.la \
		       terms/libterms.la

