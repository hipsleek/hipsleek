# HIP without slicing
./run-fast-tests.pl slicing -log-timings -tp om -flags "--eps --force_one_slice --force_one_slice_proving"

# HIP with automatic slicing
./run-fast-tests.pl slicing -log-timings -tp om -flags "--eps"

#./run-fast-tests.pl slicing -log-timings -tp om -flags "--eps --enable-slicing --opt-imply 0"
#./run-fast-tests.pl slicing -log-timings -tp om -flags "--eps --enable-slicing --opt-imply 1"
# HIP with forced slicing (without heuristic)
./run-fast-tests.pl slicing -log-timings -tp om -flags "--eps --enable-slicing --slc-opt-imply 2"

# HIP with forced slicing (with heuristic)
./run-fast-tests.pl slicing -log-timings -tp om -flags "--eps --enable-slicing --slc-opt-imply 3"