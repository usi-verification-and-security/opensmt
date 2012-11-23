echo "[Reverting up src/tsolvers/.Makefile.am as src/tsolvers/Makefile.am]"
cp -f src/tsolvers/.Makefile.am src/tsolvers/Makefile.am
echo "[Reverting up src/parsers/smt/.smtparser.yy as src/parsers/smt/smtparser.yy]"
cp -f src/parsers/smt/.smtparser.yy src/parsers/smt/smtparser.yy
echo "[Reverting up src/egraph/.EgraphSolver.C as src/egraph/EgraphSolver.C]"
cp -f src/egraph/.EgraphSolver.C src/egraph/EgraphSolver.C
echo "[Reverting up src/simplifiers/.TopLevelProp.C as src/simplifiers/TopLevelProp.C]"
cp -f src/simplifiers/.TopLevelProp.C src/simplifiers/TopLevelProp.C
echo "[Reverting up src/common/.Global.h as src/common/Global.h]"
cp -f src/common/.Global.h src/common/Global.h
echo "[Reverting up .configure.ac as configure.ac]"
cp -f .configure.ac configure.ac
echo "[Removing solver dir]"
rm -fr src/tsolvers/niasolver
echo "Reconfiguring"
autoreconf &> /dev/null
echo "***********************************************"
echo "  Done                                         "
echo "***********************************************"
