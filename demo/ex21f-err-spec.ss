void failmeth (int x)
 requires x<0
 ensures true;
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
    failmeth(x);
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


*/
