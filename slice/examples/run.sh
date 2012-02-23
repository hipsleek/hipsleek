for (( i = 1; i <= 3; i++ ))
do
	time ./run-fast-tests.pl pomega -flags "--eps --dis-slicing" --log-timings
	time ./run-fast-tests.pl pomega -flags "--eps" --log-timings

	time ./run-fast-tests.pl pz3 -flags "--eps --dis-slicing" --log-timings -tp z3
	time ./run-fast-tests.pl pz3 -flags "--eps" --log-timings -tp z3

	time ./run-fast-tests.pl pmona -flags "--eps --dis-slicing" --log-timings -tp mona
	time ./run-fast-tests.pl pmona -flags "--eps" --log-timings -tp mona

	time ./run-fast-tests.pl pmona -flags "--eps --dis-slicing" --log-timings -tp om
	time ./run-fast-tests.pl pmona -flags "--eps" --log-timings -tp om

	time ./run-fast-tests.pl pmona -flags "--eps --dis-slicing" --log-timings -tp zm
	time ./run-fast-tests.pl pmona -flags "--eps" --log-timings -tp zm

	time ./run-fast-tests.pl plink -flags "--eps --dis-slicing" --log-timings -tp om
	time ./run-fast-tests.pl plink -flags "--eps" --log-timings -tp om
	time ./run-fast-tests.pl plink -flags "--eps --enable-slicing" --log-timings -tp om

	time ./run-fast-tests.pl plink -flags "--eps --dis-slicing" --log-timings -tp zm
	time ./run-fast-tests.pl plink -flags "--eps" --log-timings -tp zm
	time ./run-fast-tests.pl plink -flags "--eps --enable-slicing" --log-timings -tp zm

	mv timings_log.xls timings_log_$i.xls
done

