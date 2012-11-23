#!/bin/sh
# $Id: autogen.sh,v 1.1 2007-11-08 15:49:18 aehyvari Exp $
aclocal -I m4\
&& libtoolize --force \
&& automake --foreign --add-missing \
&& autoconf
