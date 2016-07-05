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
  ensures stk::RS<m> * stk_mark::RS_bnd<m,m> 
   * stk_min::RS_min<m> * stk_max::RS_max<m> & m=a+n;

void sub_stk(int n)
  requires stk::RS<a> & n>=0 & a>=n
  ensures stk::RS<a-n>;

bool rand()
 requires true
 ensures res or !res;

/*
Checking procedure f$RS~RS_max~RS_min~RS_bnd... 
Procedure f$RS~RS_max~RS_min~RS_bnd FAIL-2

Exception Failure("hd") Occurred!
*/

void g1() 
//requires stk::RS<n> 
// ensures  stk::RS<n> * stk_mark::RS_bnd<m,h> & m>=n+1 & h<=n+4;
  requires stk::RS<n> 
  ensures  stk::RS<n> * stk_min::RS_min<m> * stk_max::RS_max<h>
     & m>=n+1 & h<=n+4;

void g2() 
//  requires stk::RS<n> 
//  ensures  stk::RS<n> * stk_mark::RS_bnd<m,h> & m>=n+2 & h<=n+3;
  requires stk::RS<n> 
  ensures  stk::RS<n> * stk_min::RS_min<m> * stk_max::RS_max<h> 
     & m>=n+2 & h<=n+3;

// seems less precise when combined!
// cannot verify with m>=n+4 & h<=n+6
void f() 
//  requires stk::RS<n>
//  ensures  stk::RS<n> * stk_mark::RS_bnd<m,h> 
//    & m>=n+3 & h<=n+6;
  requires stk::RS<n>
  ensures  stk::RS<n> * stk_min::RS_min<m> * stk_max::RS_max<h> 
    & m>=n+4 & h<=n+6;
{
  add_stk(2); //add stack frame used
  g1(); g2();
  //dprint;
  sub_stk(2); //add stack frame used
}
