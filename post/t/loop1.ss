int PastaA1_main()
//infer [@post_n]
  requires true
  ensures res=10;
{
  int x;
  x=10;
  int y = 0;
    while (y < x) 
      //infer [@post_n]
      requires true
      ensures (y<x & y'=x & x'=x | y>=x & y'=y & x'=x);
    {
      y++;
    }
  return y; 
}

/*
# loop1.ss

 where did this warning come from?

WARNING: t/loop1.ss_12:16_12:42:the result type __norm is not covered by the throw list[__Brk_top]

*/
