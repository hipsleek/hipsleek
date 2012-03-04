rm timings_log.xls

for (( i = 1; i <= 1; i++ ))
do
	# time ./run-fast-tests.pl pomega -flags "--eps --dis-slicing" --log-timings
	# time ./run-fast-tests.pl pomega -flags "--eps" --log-timings

	# time ./run-fast-tests.pl pz3 -flags "--eps --dis-slicing" --log-timings -tp z3
	# time ./run-fast-tests.pl pz3 -flags "--eps" --log-timings -tp z3

	# time ./run-fast-tests.pl pmona -flags "--eps --dis-slicing" --log-timings -tp mona
	# time ./run-fast-tests.pl pmona -flags "--eps" --log-timings -tp mona

	# time ./run-fast-tests.pl pmona -flags "--eps --dis-slicing" --log-timings -tp om
	# time ./run-fast-tests.pl pmona -flags "--eps" --log-timings -tp om

	# time ./run-fast-tests.pl pmona -flags "--eps --dis-slicing" --log-timings -tp zm
	# time ./run-fast-tests.pl pmona -flags "--eps" --log-timings -tp zm

	# time ./run-fast-tests.pl plink -flags "--eps --dis-slicing" --log-timings -tp om
	# time ./run-fast-tests.pl plink -flags "--eps" --log-timings -tp om
	# time ./run-fast-tests.pl plink -flags "--eps --enable-slicing" --log-timings -tp om

	# time ./run-fast-tests.pl plink -flags "--eps --dis-slicing" --log-timings -tp zm
	# time ./run-fast-tests.pl plink -flags "--eps" --log-timings -tp zm
	# time ./run-fast-tests.pl plink -flags "--eps --enable-slicing" --log-timings -tp zm
	
	# Omega
	# time ./run-fast-tests.pl pomega -flags "--eps --dis-imm --dfe --dis-slicing" --log-timings
	# time ./run-fast-tests.pl pomega -flags "--eps --dis-imm --dfe" --log-timings

	time ./run-fast-tests.pl pomega -flags "--eps --dfe --dis-slicing --ep-stat" --log-timings -stat
	time ./run-fast-tests.pl pomega -flags "--eps --dfe --ep-stat" --log-timings -stat
	
	# Z3
	# time ./run-fast-tests.pl pz3 -flags "--eps --dis-imm --dfe --dis-slicing" --log-timings -tp z3
	# time ./run-fast-tests.pl pz3 -flags "--eps --dis-imm --dfe" --log-timings -tp z3
	
	time ./run-fast-tests.pl pz3 -flags "--eps --dfe --dis-slicing --ep-stat" --log-timings -tp z3 -stat
	time ./run-fast-tests.pl pz3 -flags "--eps --dfe --ep-stat" --log-timings -tp z3 -stat

	# Mona
	# time ./run-fast-tests.pl pmona -flags "--eps --dis-imm --dfe --dis-slicing" --log-timings -tp mona
	# time ./run-fast-tests.pl pmona -flags "--eps --dis-imm --dfe" --log-timings -tp mona

	time ./run-fast-tests.pl pmona -flags "--eps --dfe --dis-slicing --ep-stat" --log-timings -tp mona -stat
	time ./run-fast-tests.pl pmona -flags "--eps --dfe --ep-stat" --log-timings -tp mona -stat

	# Redlog
	time ./run-fast-tests.pl predlog -flags "--dis-oc --eps --dfe --dis-slicing --ep-stat" --log-timings -tp redlog -stat
	time ./run-fast-tests.pl predlog -flags "--dis-oc --eps --dfe --ep-stat" --log-timings -tp redlog -stat

	# OM
	# time ./run-fast-tests.pl plink -flags "--eps --dis-imm --dfe --dis-slicing" --log-timings -tp om
	# time ./run-fast-tests.pl plink -flags "--eps --dis-imm --dfe" --log-timings -tp om
	# time ./run-fast-tests.pl plink -flags "--eps --dis-imm --enable-slicing" --log-timings -tp om

	time ./run-fast-tests.pl plink -flags "--eps --dfe --dis-slicing --ep-stat" --log-timings -tp om -stat
	time ./run-fast-tests.pl plink -flags "--eps --dfe --ep-stat" --log-timings -tp om -stat
	time ./run-fast-tests.pl plink -flags "--eps --dfe --enable-slicing --ep-stat" --log-timings -tp om -stat

	# ZM
	# time ./run-fast-tests.pl plink -flags "--eps --dis-imm --dfe --dis-slicing" --log-timings -tp zm
	# time ./run-fast-tests.pl plink -flags "--eps --dis-imm --dfe" --log-timings -tp zm
	# time ./run-fast-tests.pl plink -flags "--eps --dis-imm --enable-slicing" --log-timings -tp zm

	time ./run-fast-tests.pl plink -flags "--eps --dfe --dis-slicing --ep-stat" --log-timings -tp zm -stat
	time ./run-fast-tests.pl plink -flags "--eps --dfe --ep-stat" --log-timings -tp zm -stat
	time ./run-fast-tests.pl plink -flags "--eps --dfe --enable-slicing --ep-stat" --log-timings -tp zm -stat

	# SIR
	time ./run-fast-tests.pl SIR -flags "--eps --dfe --dis-slicing --ep-stat" --log-timings -stat
	time ./run-fast-tests.pl SIR -flags "--eps --dfe --ep-stat" --log-timings -stat

	mv timings_log.xls timings_log_$(date +%Y%m%d_%H%M%S).xls
done

