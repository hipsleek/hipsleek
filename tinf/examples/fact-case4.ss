int fact(int x)
 case {
  //x=0 -> ensures res=1;
  x>0 -> ensures res>=1;
  //x<0 -> requires false ensures false;
}
{
  if (x==0) return 1;
  else return 1 + fact(x - 1);
}
/*
# fact-case4.ss --pcp

For this example, it seems better to give a
case-pattern warning as opposed to having a pre-cond failure.

Can we check if missing case-pattern is unreachable?

# DONE with warning

*/
