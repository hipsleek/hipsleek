pred_prim RS<high:int>
  inv high>=0;

pred_prim RS_mark<high:int>
  inv 0<=high;

//global RS_bnd stk_mark;
global RS stk;
global RS_mark mx;

lemma "combine2" 
self::RS_mark<m1>*self::RS_mark<m2> 
  -> self::RS_mark<m> & m=max(m1,m2);

// add back space into stack
void add_stk(int n)
  requires stk::RS<a> & n>=0
  ensures stk::RS<m> * mx::RS_mark<m> & m=a+n;

void sub_stk(int n)
  requires stk::RS<a> & n>=0 & a>=n
  ensures stk::RS<a-n>;

/*
bool rand()
 requires true
 ensures res or !res;
*/
/*
void g() 
  requires stk::RS<n> 
  ensures  stk::RS<n> * mx::RS_mark<h> & h<=n+2 ;
{
  add_stk(2); //add stack frame used
  sub_stk(2); //add stack frame used
}
*/

//relation RR(int n, int m).

void h() 
  //infer [RR]
  requires stk::RS<nn> 
  ensures  stk::RS<nn> * mx::RS_mark<hh> & hh<=nn+3;
{
  add_stk(3); //add stack frame used
  sub_stk(3); //add stack frame used
}

/*
void f() 
  requires stk::RS<n>
  ensures  stk::RS<n> * mx::RS_mark<h>
//    & m>=n+3+2 & h<=n+5+2;
  & h<=n+3+2; // valid
{
  add_stk(2); //add stack frame used
  g(); h();
  //h(); g();
  //dprint;
  sub_stk(2); //add stack frame used
}
*/

