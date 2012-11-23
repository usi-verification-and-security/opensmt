#!/bin/bash
#
# Author: Roberto Bruttomesso
#
# Description: Given a name for a solver and a directory 
#              to be put in, the script automatically
#              sets up directories, Makefiles, and so on
# 
# Usage: sh create_tsolver.sh <solver name> <solver subdir>
#

# Checks that input parameters is exactly 2
if [ $# -ne 3 ]; then
  echo "Usage: sh create_tsolver.sh <solver name> <solver dir> <logic>" 
  echo "Example: sh create_tsolver.sh MySolver mysolver MYLOGIC" 
  exit 1
fi

name=$1

# Some names cannot be used, as they clash with existing software constructs
# TODO: The list is incomplete
if [[ $name = "TSolver" || $name = "tsolver" ]]; then
  echo "Can't create solver: given name is forbidden"
fi

namelower=`echo $1 | tr "[:upper:]" "[:lower:]"`
nameupper=`echo $1 | tr "[:lower:]" "[:upper:]"`
dir=$2
logic=$3

# Checks that the directory does not exists
if [ -d src/tsolvers/$dir ]; then
  echo "Can't create solver: directory already exists"
  exit 1
fi

# Creates directory
mkdir src/tsolvers/$dir

# Copy empty solver as src/tsolvers/$dir
echo "Creating src/tsolvers/$dir/$name.C src/tsolvers/$dir/$name.h"
cp src/tsolvers/emptysolver/EmptySolver.C src/tsolvers/$dir/$name.C
cp src/tsolvers/emptysolver/EmptySolver.h src/tsolvers/$dir/$name.h

# Copy Makefile
echo "Creating src/tsolvers/$dir/Makefile.am"
cp src/tsolvers/emptysolver/Makefile.am src/tsolvers/$dir

# Adapt sources and Makefile
sed -i s/EmptySolver/$name/g src/tsolvers/$dir/*
sed -i s/emptysolver/$namelower/g src/tsolvers/$dir/Makefile.am 
sed -i s/EMPTYSOLVER/$nameupper/g src/tsolvers/$dir/$name.h

echo "[Backing up src/tsolvers/Makefile.am as src/tsolvers/.Makefile.am]"
cp -f src/tsolvers/Makefile.am src/tsolvers/.Makefile.am
echo "[Backing up src/parsers/smt/smtparser.yy as src/parsers/smt/.smtparser.yy]"
cp -f src/parsers/smt/smtparser.yy src/parsers/smt/.smtparser.yy
echo "[Backing up src/egraph/EgraphSolver.C as src/egraph/.EgraphSolver.C]"
cp -f src/egraph/EgraphSolver.C src/egraph/.EgraphSolver.C
echo "[Backing up src/simplifiers/TopLevelProp.C as src/simplifiers/.TopLevelProp.C]"
cp -f src/simplifiers/TopLevelProp.C src/simplifiers/.TopLevelProp.C
echo "[Backing up src/common/Global.h as src/common/.Global.h]"
cp -f src/common/Global.h src/common/.Global.h
echo "[Backing up configure.ac as .configure.ac]"
cp -f configure.ac .configure.ac

# Adjusting src/tsolvers/Makefile.am
echo "Modifying src/tsolvers/$dir/Makefile.am"
subdirs=`grep SUBDIRS src/tsolvers/Makefile.am`
middle="noinst_LTLIBRARIES = libtsolvers.la\n\nINCLUDES=\$(config_includedirs)\n\nlibtsolvers_la_SOURCES = TSolver.h THandler.C THandler.h"
libadd=`grep LIBADD src/tsolvers/Makefile.am`
echo "$subdirs $dir" > src/tsolvers/Makefile.am
echo >> src/tsolvers/Makefile.am
echo -e $middle >> src/tsolvers/Makefile.am
echo "$libadd $dir/lib$namelower.la" >> src/tsolvers/Makefile.am

# Adjusting src/parsers/smt/smtparser.yy
echo "Modifying src/parsers/smt/smtparser.yy"
parseinit="NEW_THEORY_INIT\n                     else if ( strcmp( \$2, \"$logic\" ) == 0 ) parser_config->logic = $logic;\n"
sed -i s/NEW_THEORY_INIT/"$parseinit"/ src/parsers/smt/smtparser.yy

# Adjusting src/egraph/EgraphSolver.C
echo "Modifying src/egraph/EgraphSolver.C"
egraphheader="NEW_THEORY_HEADER\n#include \"$name.h\"";
sed -i s/NEW_THEORY_HEADER/"$egraphheader"/ src/egraph/EgraphSolver.C
egraphinit="NEW_THEORY_INIT\n  else if ( config.logic == $logic )\n  {\n    tsolvers.push_back( new $name( tsolvers.size( ), \"$name\", config, *this, explanation, deductions, suggestions ) );\n#ifdef STATISTICS\n     tsolvers_stats.push_back( new TSolverStats( ) );\n#endif\n  }";
sed -i s/NEW_THEORY_INIT/"$egraphinit"/ src/egraph/EgraphSolver.C

# Adjusting src/simplifiers/TopLevelProp.C
echo "Modifying src/simplifiers/TopLevelProp.C"
toplevelpropinit="NEW_THEORY_INIT\n       else if ( config.logic == $logic )\n ; \/\/ Do nothing"
sed -i s/NEW_THEORY_INIT/"$toplevelpropinit"/ src/simplifiers/TopLevelProp.C

# Adjusting src/common/Global.h
echo "Modifying src/common/Global.h"
globalinit="NEW_THEORY_INIT\n   , $logic"
sed -i s/NEW_THEORY_INIT/"$globalinit"/ src/common/Global.h

# Adjusting configure.ac
echo "Modifying configure.ac"
awk -v dirawk=$dir '// { if ( $0 ~ /-I\\\${top_srcdir}\/src\/tsolvers \\\\\\/ ) printf("%s\n%s%s%s\n", $0, "-I\\${top_srcdir}/src/tsolvers/", dirawk, " \\\\\\" ); else print $0; }' configure.ac > /tmp/conf.tmp
cp /tmp/conf.tmp configure.ac
awk -v dirawk=$dir '// { if ( $0 ~ /src\/tsolvers\/Makefile \\/ ) printf("%s\n%s%s%s\n", $0, "                  src/tsolvers/", dirawk, "/Makefile \\" ); else print $0; }' configure.ac > /tmp/conf.tmp
cp /tmp/conf.tmp configure.ac

echo "Reconfiguring"
autoreconf &> /dev/null

echo "Producing revert_last.sh script"
rm -f revert_last.sh
echo 'echo "[Reverting up src/tsolvers/.Makefile.am as src/tsolvers/Makefile.am]"' >> revert_last.sh
echo 'cp -f src/tsolvers/.Makefile.am src/tsolvers/Makefile.am' >> revert_last.sh
echo 'echo "[Reverting up src/parsers/smt/.smtparser.yy as src/parsers/smt/smtparser.yy]"' >> revert_last.sh
echo 'cp -f src/parsers/smt/.smtparser.yy src/parsers/smt/smtparser.yy' >> revert_last.sh
echo 'echo "[Reverting up src/egraph/.EgraphSolver.C as src/egraph/EgraphSolver.C]"' >> revert_last.sh
echo 'cp -f src/egraph/.EgraphSolver.C src/egraph/EgraphSolver.C' >> revert_last.sh
echo 'echo "[Reverting up src/simplifiers/.TopLevelProp.C as src/simplifiers/TopLevelProp.C]"' >> revert_last.sh
echo 'cp -f src/simplifiers/.TopLevelProp.C src/simplifiers/TopLevelProp.C' >> revert_last.sh
echo 'echo "[Reverting up src/common/.Global.h as src/common/Global.h]"' >> revert_last.sh
echo 'cp -f src/common/.Global.h src/common/Global.h' >> revert_last.sh
echo 'echo "[Reverting up .configure.ac as configure.ac]"' >> revert_last.sh
echo 'cp -f .configure.ac configure.ac' >> revert_last.sh
echo 'echo "[Removing solver dir]"' >> revert_last.sh
echo "rm -fr src/tsolvers/$dir" >> revert_last.sh
echo 'echo "Reconfiguring"' >> revert_last.sh
echo 'autoreconf &> /dev/null' >> revert_last.sh
echo 'echo "***********************************************"' >> revert_last.sh
echo 'echo "  Done                                         "' >> revert_last.sh
echo 'echo "***********************************************"' >> revert_last.sh
chmod 755 revert_last.sh

echo "***********************************************"
echo "  Done                                         "
echo "***********************************************"
echo "                                               "
echo "  Don't forget to adjust/implement methods in  "
echo "  src/tsolvers/$dir                            "
echo "  Use revert_last.sh to restore to the         "
echo "  previous state                               "
echo "                                               "
echo "***********************************************"
