int double(int n)
  requires n>=0 & Term[n]
  ensures  res=2*n & res>=0;
  requires n<0 & Loop
  ensures  false;
{
  if (n==0) return 0;
  else return 2+double(n-1);
}

/*
# ex1a.ss

There is no transition but yet an error!

Termination checking result: 
(8)->(8) (ERR: invalid transition)  Term[17; n] ->  Loop{ 1:0}[]

see # ex1c-double-term.slk

checkentail !(v_bool_7_1324') & n'!=0 & 0<=n & n'=n & v_int_8_1322'=2 & 
v_int_8_1319'+1=n' & Term
 |-  emp&v_int_8_1319'<0 & Loop.

Entail 1: Fail.(must) cause: 0<=(1+v_int_8_1319') & (1+v_int_8_1319')!=0 |-  v_int_8_1319'<0. LOCS:[1;2;3] (must-bug)
<1>: (3) (ERR: invalid transition)  Term[] ->  Loop{ 0:0}[]
*/
