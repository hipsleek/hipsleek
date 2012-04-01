#create a list of expected results
echo "======= ptr-byval.ss ======"
../hip ptr-byval.ss > 'test/ptr-byval.res'
echo "======= ptr-byref.ss ======"
../hip ptr-byref.ss > 'test/ptr-byref.res'
