void failmeth (int x)
 requires x<0
 ensures true;

void failmeth2 (int x)
 requires true
 ensures true & flow __Error;
/*
 case {
  x<0 -> ensures true;
  x>=0 -> ensures true & flow __MayError;
 }
*/

void foo(int x)
  requires true
  ensures true;
{
  if (x>0) {
    //failmeth(x);
    failmeth2(x);
    //assert false assume true;
    dprint;
    //assert false;
    //assert x'<0;
  }
  dprint;
}

/*
# ex21b


 {x>=0 & MayErr} \/ {x<=0 & norm}
 ==>
 {x>=0 & MayErr \/ false & MayErr} \/ {false & norm \/ x<=0 & norm}
 ==>
 {x>=0 & MayErr} \/ {x<=0 & norm}


Escaped States:
[
 
 Try-Block:0::
 [
  Path: [(,0 ); (,1 )]
  State:htrue&v_bool_15_1397' & 0<x' & x'=x&{FLOW,(6,10)=__Error#E}[]

  ]
 ]
Successful States:
[
 Label: [(,1 ); (,2 )]
 State:htrue&x'=x & x<=0&{FLOW,(4,5)=__norm#E}[]

 ]

*/
