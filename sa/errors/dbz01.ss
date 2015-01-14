
 relation P(int a).
 relation Q(int a, int b).

int foo(int z)
 //  infer [@error] requires z>=0 ensures res>0;
   infer [P,Q] requires z>=0 & P(z) ensures res>0 & Q(z,res);
{
  return 2/z;
}
