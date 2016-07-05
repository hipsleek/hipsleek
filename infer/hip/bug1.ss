// BUG : why did post-condition has a weird form 0<:i'?

void foo2(ref int i)
  infer [i]
  requires true
  ensures true;
/* expecting
 requires i>1
 ensures i-2<=i'<=i-1; //'
Inferred Pure:[ 2<=i]
Residual Post : [ true & i=i'+r_24' & 1<=r_24' & ((0 <: i')+2)<=r_24' & r_24'<=2 &
{FLOW,(20,21)=__norm}]
*/
{
  int r;
  //assume 1<=r<=2; 
  ass(r);
  i = i-r;
  //dprint;
  bnd(i);
}


void bnd(int i)
 requires i>=0
 ensures true;

void ass(ref int r)
 requires true
 ensures 1<=r'<=2;
