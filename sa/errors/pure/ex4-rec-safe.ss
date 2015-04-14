
relation P(int a).
relation Q(int a).


int foo(int n)
//infer [P] requires P(n) ensures true & flow __Error;
infer [P] requires P(n) ensures true & flow __norm;
                        /* case { n>=3 ->  ensures true & flow __Error;
  n<3  -> ensures true;
  }
                        */
{

  if (n < 3) {
    return 0;
  }
  else {
    // dprint;
    foo(n-1);
    //dprint;
    __error();
    //dprint;
    return 1;
  }
}
