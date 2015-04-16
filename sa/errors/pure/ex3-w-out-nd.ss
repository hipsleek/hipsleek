

bool bool_nd()
requires true
  ensures true;

void __error()
  requires  true
  ensures  true & flow __Error;


relation P1(int a).
relation P(int a).
relation Q(int a, int b).


void foo(int x)
  infer [P] requires P(x) ensures true;// & flow __Error;
{
  //dprint;
  x=0;
  //  dprint;
  while(x<10)
     infer [P1,Q] requires P1(x) ensures Q(x,x') & x'=10;
    /* case { */
    /* x>=10 -> ensures x'=x; */
    /* x<10 ->  ensures x'>=x; */
    /* }; */
    {
    if (bool_nd()) break;
    x++;
  }
     dprint;
  assert (x' !=10);
  //__error();
}
