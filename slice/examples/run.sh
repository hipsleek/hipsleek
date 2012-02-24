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
	
	time ./run-fast-tests.pl pomega -flags "--eps --dis-imm --dfe --dis-slicing" --log-timings
	time ./run-fast-tests.pl pomega -flags "--eps --dis-imm --dfe" --log-timings
	
	time ./run-fast-tests.pl pomega -flags "--eps --dfe --dis-slicing" --log-timings
	time ./run-fast-tests.pl pomega -flags "--eps --dfe" --log-timings
	
	time ./run-fast-tests.pl pz3 -flags "--eps --dis-imm --dfe --dis-slicing" --log-timings -tp z3
	time ./run-fast-tests.pl pz3 -flags "--eps --dis-imm --dfe" --log-timings -tp z3
	
	time ./run-fast-tests.pl pz3 -flags "--eps --dfe --dis-slicing" --log-timings -tp z3
	time ./run-fast-tests.pl pz3 -flags "--eps --dfe" --log-timings -tp z3
	
	time ./run-fast-tests.pl pmona -flags "--eps --dis-imm --dfe --dis-slicing" --log-timings -tp mona
	time ./run-fast-tests.pl pmona -flags "--eps --dis-imm --dfe" --log-timings -tp mona

	time ./run-fast-tests.pl pmona -flags "--eps --dfe --dis-slicing" --log-timings -tp mona
	time ./run-fast-tests.pl pmona -flags "--eps --dfe" --log-timings -tp mona

	time ./run-fast-tests.pl plink -flags "--eps --dis-imm --dfe --dis-slicing" --log-timings -tp om
	time ./run-fast-tests.pl plink -flags "--eps --dis-imm --dfe" --log-timings -tp om
	time ./run-fast-tests.pl plink -flags "--eps --dis-imm --enable-slicing" --log-timings -tp om

	time ./run-fast-tests.pl plink -flags "--eps --dfe --dis-slicing" --log-timings -tp om
	time ./run-fast-tests.pl plink -flags "--eps --dfe" --log-timings -tp om
	time ./run-fast-tests.pl plink -flags "--eps --enable-slicing" --log-timings -tp om

	time ./run-fast-tests.pl plink -flags "--eps --dis-imm --dfe --dis-slicing" --log-timings -tp zm
	time ./run-fast-tests.pl plink -flags "--eps --dis-imm --dfe" --log-timings -tp zm
	time ./run-fast-tests.pl plink -flags "--eps --dis-imm --enable-slicing" --log-timings -tp zm

	time ./run-fast-tests.pl plink -flags "--eps --dfe --dis-slicing" --log-timings -tp zm
	time ./run-fast-tests.pl plink -flags "--eps --dfe" --log-timings -tp zm
	time ./run-fast-tests.pl plink -flags "--eps --enable-slicing" --log-timings -tp zm	

	mv timings_log.xls timings_log_$(date +%Y%m%d_%H%M%S).xls
done

