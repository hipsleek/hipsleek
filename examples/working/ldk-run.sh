set -x

echo "*************************************"
echo "*************************************"
./run-fast-tests.pl sleek
echo "*************************************"
# ./run-fast-tests.pl sleek -flags "--eps --dis-para"
./run-fast-tests.pl sleek -flags "--eps"

echo "*************************************"
echo "*************************************"
#./run-fast-tests.pl hip -flags "--dis-para" #VERY SLOW
# ./run-fast-tests.pl hip -flags "--eps --dis-para"
./run-fast-tests.pl hip -flags "--eps"

echo "*************************************"
echo "*************************************"
# ./run-fast-tests.pl sleek_fracperm
./run-fast-tests.pl sleek_fracperm -flags "--en-para -tp parahip"

echo "*************************************"
echo "*************************************"
# ./run-fast-tests.pl sleek_vperm
./run-fast-tests.pl sleek_vperm -flags "--en-para -tp parahip"
echo "*************************************"
# ./run-fast-tests.pl sleek_vperm -flags "--eps"
./run-fast-tests.pl sleek_vperm -flags "--en-para -tp parahip --eps"

echo "*************************************"
echo "*************************************"
# ./run-fast-tests.pl hip_vperm
./run-fast-tests.pl hip_vperm -flags "--en-para -tp parahip"
echo "*************************************"
# ./run-fast-tests.pl hip_vperm -flags "--eps"
./run-fast-tests.pl hip_vperm -flags "--eps --en-para -tp parahip"

echo "*************************************"
echo "*************************************"
# ./run-fast-tests.pl parahip
./run-fast-tests.pl parahip -flags "--en-para -tp parahip"
echo "*************************************"
# ./run-fast-tests.pl parahip -flags "--eps"
./run-fast-tests.pl parahip -flags "--en-para -tp parahip --eps"
