# compare expected outcomes (*.res) with new outcomes
echo "======= ptr-byptr.ss ======"
diff test/ptr-byptr.res test/ptr-byptr.n
echo "======= ptr-byval.ss ======"
diff test/ptr-byval.res test/ptr-byval.n
echo "======= ptr-byref.ss ======"
diff test/ptr-byref.res test/ptr-byref.n
echo "======= ptr-globalptr.ss ======"
diff test/ptr-globalptr.res test/ptr-globalptr.n
echo "======= ptr-global.ss ======"
diff test/ptr-global.res test/ptr-global.n
echo "======= ptr-local.ss ======"
diff test/ptr-local.res test/ptr-local.n
echo "======= ptr-ifthenelse.ss ======"
diff test/ptr-ifthenelse.res test/ptr-ifthenelse.n
