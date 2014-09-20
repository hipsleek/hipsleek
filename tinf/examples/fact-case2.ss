int fact(int x)
 infer [@post_n]
 case {
  x=0 -> ensures res=1;
  x>0 -> ensures res>=1;
  x<0 -> requires false ensures false;
}
{
  if (x==0) return 1;
  else return 1 + fact(x - 1);
}
/*
# fact-case2.ss 

 infer [@post_n]
 case {
  x=0 -> ensures res=1;
  x>0 -> ensures res>=1;
  x<0 -> requires false ensures false;
}

Why isn't post-inference working?
I did  a --dd, it showed @post present but I cannot
see the post-inference outcome.

Procedure fact$int SUCCESS.

Termination checking result: SUCCESS


*/
