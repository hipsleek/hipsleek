UTPre@f fpre(int x).
UTPost@f fpost(int x).

void f(int x)
  infer [@term]
  //requires fpre(x)
  //ensures fpost(x);
/*  
  case {
    x < 0 -> requires Term ensures true;
    x >= 0 -> requires fpre(x) ensures fpost(x);
  }
*/
  case {
  x < 0 -> requires Term ensures fpost(x);
    x >= 0 -> requires fpre(x) ensures fpost(x);
  }
  
{
  if (x < 0) return;
  else f(x - 1);
}

/*
# termu-1c4.ss

why are there 4 termination assumptions?

I was expecting just 3:

infer [@term] x>=0 & fpre(x) & x'=x-1 |- fpre(x').

infer [@term] x>=0 & fpre(x) & x'=x-1 & fpost(x') |- fpost(x).

infer [@term] x<0 & Term[] |- fpost(x).


Temporal Assumptions:
 termAssume 0<=v_int_21_924 & x'=v_int_21_924+1 & !(v_bool_20_876') & 
0<=x' & !(v_bool_20_876') & x=x' & 0<=x & 
0<=x' & fpost(v_int_21_875') --> fpost(x).

 termAssume v_int_21_922<0 & x'=v_int_21_922+1 & !(v_bool_20_876') & 0<=x' & 
!(v_bool_20_876') & x=x' & 0<=x & 0<=x' & fpost(v_int_21_875') --> fpost(x).

 termAssume x'<0 & x<0 & x=x' & v_bool_20_876' & x'<0 & 
v_bool_20_876' --> fpost(x).

 termAssume 0<=x' & 0<=x & x=x' & !(v_bool_20_876') & 0<=x' & 
!(v_bool_20_876') & x'=v_int_21_875'+1 & 
0<=v_int_21_875' & fpre(x) --> fpre(v_int_21_875').

*/
