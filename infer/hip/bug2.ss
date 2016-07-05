void foo2(ref int i)
  infer [i]
  requires true
  ensures true;
/* expecting
 requires i>1
 ensures i-2<=i'<=i-1; //'
*/
{
  int r;
  //assume 1<=r<=2; 
  ass(r);
  i = i-r;
  //dprint;
  bnd(i);
}
/*
// TODO r_24' should be eliminated as it is existential
Exists Post Vars :[r_24']
OLD SPECS:  EInfer [i]
   EBase true & true & {FLOW,(20,21)=__norm}
           EAssume 7::ref [i]
             true & true & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase true & 2<=i & {FLOW,(20,21)=__norm}
         EAssume 7::ref [i]
           true & 1<=r_24' & r_24'<=2 & i'+r_24'=i & 2<=i &
           {FLOW,(20,21)=__norm}
 */


void bnd(int i)
 requires i>=0
 ensures true;

void ass(ref int r)
 requires true
 ensures 1<=r'<=2;
