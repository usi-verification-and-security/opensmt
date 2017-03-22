noinst_LTLIBRARIES = libcommon.la

AM_CPPFLAGS=$(config_includedirs)

libcommon_la_SOURCES = Otl.h \
                       TreeOps.h \
                       Global.h \
                       FastRational.h \
                       FastRational.C \
                       Timer.h

if ENABLE_LIBRARY
include_HEADERS = Alloc.h FastRational.h Global.h IntTypes.h Otl.h SigMap.h StringMap.h TreeOps.h XAlloc.h Timer.h
endif
