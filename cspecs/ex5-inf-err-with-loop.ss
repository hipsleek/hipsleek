relation P2(int n).

void error ()
  requires true
  ensures true & flow __Error;

void foo (int n)
/*
  case {
    n >= 0 -> ensures true;
    n < 0 & n + 5 >= 0 -> ensures true & flow __Error;
    n + 5 < 0 -> ensures false;
  }
*/
  infer [P2]
  requires P2(n)
  ensures n+5>=0 & flow __Error; // Segmentation fault (core dumped)
  
  //(1)
  //requires P2(n)
  //ensures false;
  
  //(2)
  //requires P2(n) & n+5>=0
  //ensures true & flow __Error;
  
  //(3)
  //requires P2(n) & n+5>=0 & !(n<0)
  //ensures true;
  
  /*
  case {
    n=0 -> ensures true;
    n!=0 -> requires P2(n) & n+5>=0 ensures true;
  }
  */
{
  if (n == 0) return;
  //else if (n == -5) error();
  else foo(n - 1); 
}


// requires P1(n) ensures false ---> n+5<0;
// requires P2(n) ensures true & __Error;  P2(n) --> not(n+5<0)
// requires P3(n) ensures true & __norm; P3(n) --> not(n+5<0)
