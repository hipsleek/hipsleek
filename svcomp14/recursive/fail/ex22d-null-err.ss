data cell {
  int val;
}

int null_err()
  requires true
  ensures true & flow __Error;
{
  cell x;
  x =null;
  return x.val;
}

bool rand() 
  requires true
  ensures !res or res;

int main()
  requires true
  ensures true & flow __norm or true & flow __Error;
{
  int r = 1;
  if (rand()) r=null_err();
  dprint;
  return r;
}



/*
# ex22d-null-err.ss

Expect success but why is there pre-cond failure?
Same as ex22b example. Why dprint not printed?

Checking procedure main$... 
Proving precondition in method null_err$ Failed.
  (must) cause: must_err (__Error#E) LOCS: [22;23]

Context of Verification Failure: 1 File "",Line:0,Col:0

Last Proving Location: 1 File "ex22d-null-err.ss",Line:23,Col:16

Procedure main$ FAIL.(2)

Exception Failure("Proving precond failed") Occurred!


*/
