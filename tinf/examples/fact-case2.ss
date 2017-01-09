int fact(int x)
//infer [@post_n]
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

Problems
(1) why is there a failure for @post_n?
(2) Why is there post-inference when we omit post_n
    (see fact-case2.ss)

Checking procedure fact$int... 
Procedure fact$int FAIL.(2)

Exception Not_found Occurred!
(Program not linked with -g, cannot print stack backtrace)

Error(s) detected when checking procedure fact$int



Why isn't post-inference working?
I did  a --dd, it showed @post present but I cannot
see the post-inference outcome.

Procedure fact$int SUCCESS.

Termination checking result: SUCCESS


*/
