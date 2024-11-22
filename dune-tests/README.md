This directory contains integration [Cram tests](https://dune.readthedocs.io/en/stable/reference/cram.html)
for HIP and SLEEK. These were initially generated using `make_hip_tests.py` and `make_sleek_tests.py`
from the old set of tests in `examples/working/`, but you do not need to run these again to add tests.

Postprocessing scripts to help filter out the outputs of HIP and SLEEK are available in `test_assets/`.
Note that these scripts have to be visible to the test, either by marking it as a dependency, or via
a directory test.


