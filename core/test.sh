#create a list of expected results
echo "======= ptr-byptr.ss ======"
../hip ptr-byptr.ss > test/ptr-byptr.res
echo "======= ptr-byval.ss ======"
../hip ptr-byval.ss > test/ptr-byval.res
echo "======= ptr-byref.ss ======"
../hip ptr-byref.ss > test/ptr-byref.res
echo "======= ptr-globalptr.ss ======"
../hip ptr-globalptr.ss > test/ptr-globalptr.res
echo "======= ptr-global.ss ======"
../hip ptr-global.ss > test/ptr-global.res
echo "======= ptr-local.ss ======"
../hip ptr-local.ss > test/ptr-local.res
echo "======= ptr-ifthenelse.ss ======"
../hip ptr-ifthenelse.ss > test/ptr-ifthenelse.res


