pred_prim RS<low:int>
  inv low>=0;

lemma "R split" self::RS<a> & p,r>=0 & a=p+r <-> self::RS<p> * self::RS<r> ;

/*
RS<min1> * RS<min2>  ==> RS<max(min1,min2)>

*/

global RS stk;

/*
void check_RS(int n)
  requires stk::RS<_,a>@L & a>=n
  ensures true;

void check_min_RS()
  requires stk::RS<m,a>@L & m<=0
  ensures true;
*/

// add back space into stack
void add_min(int n)
  requires stk::RS<a>
  ensures stk::RS<a+n>;

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

/*
Checking procedure g$RS... 
Procedure g$RS FAIL-2

Exception Failure("hd") Occurred!
*/

void g() 
  requires stk::RS<0> 
  ensures  stk::RS<3>;
{
  add_min(2); //subtract stack frame
}
