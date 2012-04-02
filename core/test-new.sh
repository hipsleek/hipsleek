#create a list of new results
#create a list of expected results
echo "======= ptr-byptr.ss ======"
../hip ptr-byptr.ss > test/ptr-byptr.n
echo "======= ptr-byval.ss ======"
../hip ptr-byval.ss > test/ptr-byval.n
echo "======= ptr-byref.ss ======"
../hip ptr-byref.ss > test/ptr-byref.n
echo "======= ptr-globalptr.ss ======"
../hip ptr-globalptr.ss > test/ptr-globalptr.n
echo "======= ptr-global.ss ======"
../hip ptr-global.ss > test/ptr-global.n
echo "======= ptr-local.ss ======"
../hip ptr-local.ss > test/ptr-local.n
echo "======= ptr-ifthenelse.ss ======"
../hip ptr-ifthenelse.ss > test/ptr-ifthenelse.n
