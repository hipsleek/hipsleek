pred_prim RS<low:int,high:int>
  inv low<=high & high>=0;

/*
lemma "R split" self::RS<a,b> & q,s>=0 & b=q+s
    & a=p+r & p<=q & r<=s <-> self::RS<p,q> * self::RS<r,s> ;
*/

global RS stk;

void check_RS(int n)
  requires stk::RS<_,a>@L & a>=n
  ensures true;

void check_min_RS()
  requires stk::RS<m,a>@L & m<=0
  ensures true;

// subtract space from stack
void sub_RS(int n)
  requires stk::RS<z,a> & a>=n
  ensures stk::RS<z-n,a-n>;

// add back space into stack
void add_RS(int n)
  requires stk::RS<z,a>
  ensures stk::RS<z+n,a+n>;
/*
void f() 
  requires stk::RS<0,m> & m=6
  ensures  stk::RS<0,m>;
{
  sub_RS(2); //subtract stack frame
  //dprint;
  g();
  add_RS(2); //add back stack frame prior to return
}
*/

void g() 
  requires stk::RS<3,m> & m=4
  ensures  stk::RS<3,m>;
{
  sub_RS(2); //subtract stack frame
  check_min_RS();
  add_RS(2); //add back stack frame prior to return
}
