SUBDIRS = parsers tsolvers smtsolvers common api sorts logics symbols pterms egraph cnfizers simplifiers

noinst_LTLIBRARIES = libopensmt.la

if WANT_LIBRARY
lib_LTLIBRARIES = libopensmt-1.0.la
endif

libopensmt_la_SOURCES =
libopensmt_la_LIBADD = parsers/libparsers.la \
		       tsolvers/libtsolvers.la \
		       smtsolvers/libsmtsolvers.la \
		       common/libcommon.la \
		       sorts/libsorts.la \
		       simplifiers/libsimplifiers.la \
		       api/libapi.la \
		       logics/liblogics.la \
		       symbols/libsymbols.la \
		       pterms/libpterms.la \
		       egraph/libegraph.la \
		       cnfizers/libcnfizers.la

libopensmt_1_0_la_SOURCES = 
libopensmt_1_0_la_LIBADD = smtsolvers/libsmtsolvers.la \
		       common/libcommon.la \
		       sorts/libsorts.la \
		       api/libapi.la \
		       logics/liblogics.la \
		       symbols/libsymbols.la \
		       pterms/libpterms.la \
		       egraph/libegraph.la \
		       cnfizers/libcnfizers.la

