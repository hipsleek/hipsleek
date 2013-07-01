// this used a single predicate to mark lower/upper stack bound
// for a given method; and it is specified in the post-condition

pred_prim RS<low:int>
  inv low>=0;

pred_prim RS_bnd<low:int,high:int>
  inv 0<=low<=high;

pred_prim RS_min<low:int>
  inv 0<=low;

pred_prim RS_max<high:int>
  inv 0<=high;

global RS_bnd stk_mark;
global RS_min stk_min;
global RS_max stk_max;
global RS stk;

// add back space into stack
void add_stk(int n)
  requires stk::RS<a> & n>=0
  ensures stk::RS<m> 
    //* stk_mark::RS_bnd<m,m> & m=a+n;
    //* stk_min::RS_min<m> 
    * stk_max::RS_max<m> & m=a+n;

void sub_stk(int n)
  requires stk::RS<a> & n>=0 & a>=n
  ensures stk::RS<a-n>;


void g1() 
  requires stk::RS<n> 
  ensures  stk::RS<n> * stk_max::RS_max<h> & h<=n+4;
 
void g2() 
  requires stk::RS<n> 
  ensures  stk::RS<n> * stk_max::RS_max<h> &  h<=n+3;

// must use RS_max<h1>*RS_max<h2> ==> RS_max<min(h1,h2)>
// must use RS_min<h1>*RS_min<h2> ==> RS_max<max(h1,h2)>

// seems less precise when combined!
// cannot verify with m>=n+4 & h<=n+6
void f() 
  requires stk::RS<n>
  ensures  stk::RS<n> * stk_max::RS_max<h>  
     & h<=n+2; // unsound on upper bound!
{
  add_stk(2); //add stack frame used
  g1(); g2();
  dprint;
  sub_stk(2); //add stack frame used
}
