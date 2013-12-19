int foo (int x)
 requires x<0 or x=0 or x>0
 ensures  res=2*x;
{
	if (x==0)
		return 0;
	else
		return 2+foo(x-1);
}
/*
# valid-1a-nocase.ss

 checkentail Base emp&0<x & x=x' & x'!=0 & !(v_bool_5_865') 
    & x'!=0 & !(v_bool_5_865') & v_int_8_863'=2 
    & x'=v_int_8_861'+1&{FLOW,(24,25)=__norm}[]
 |-  Base emp&v_int_8_861'=0&{FLOW,(24,25)=__norm}[]. 

*/

/*
 requires x<0 or x>=0
 ensures  res=2*x;
 //ok

 requires x<0 or x=0 or x>0
 ensures  res=2*x;
//pre-cond failure

 requires x<0 & Loop or x>=0 & Term[x]
 ensures  res=2*x;
//valid

 requires x<0 & Loop or x=0 & Term[] or x>0 & Term[x]
 ensures  res=2*x;

 fail pre + but gave an incorrect non-decreasing message?

Termination checking result:  (3)->(20) (MayTerm ERR: not decreasing) Term[29; pv_868] -> Term[29; pv_868]

*/
//ensures  x=0 & res=0 or x>0 & res=2*x;
/*
 ensures x<0 & false or 
 case {
	x<0 -> requires Loop 
           ensures false;
	x=0 -> requires Term[] 
           ensures res=0;
	x>0 -> requires Term[x] 
           ensures res=2*x;
 }
*/
