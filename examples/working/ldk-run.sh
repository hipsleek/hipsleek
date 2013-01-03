set -x

echo "*************************************"
echo "*************************************"
./run-fast-tests.pl sleek
echo "*************************************"
./run-fast-tests.pl sleek -flags "--eps --dis-para"
echo "*************************************"
echo "*************************************"
#./run-fast-tests.pl hip -flags "--dis-para" #VERY SLOW
./run-fast-tests.pl hip -flags "--eps --dis-para"
echo "*************************************"
echo "*************************************"
./run-fast-tests.pl sleek_fracperm
echo "*************************************"
echo "*************************************"
./run-fast-tests.pl sleek_vperm
echo "*************************************"
./run-fast-tests.pl sleek_vperm -flags "--eps"
echo "*************************************"
echo "*************************************"
./run-fast-tests.pl hip_vperm
echo "*************************************"
./run-fast-tests.pl hip_vperm -flags "--eps"
echo "*************************************"
echo "*************************************"
./run-fast-tests.pl parahip
echo "*************************************"
./run-fast-tests.pl parahip -flags "--eps"
