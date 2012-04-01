#create a list of new results
#create a list of expected results
echo "======= ptr-byval.ss ======"
../hip ptr-byval.ss > 'test/ptr-byval.n'
echo "======= ptr-byref.ss ======"
../hip ptr-byref.ss > 'test/ptr-byref.n'
