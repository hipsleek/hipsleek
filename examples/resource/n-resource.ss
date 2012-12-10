pred_prim R<high:int>
  inv high>=0;

global R stk;

void check_stk(int n)
  requires stk::R<a>@L & a>=n
  ensures true;

void subtr_stk(int n)
  requires stk::R<a> & a>=n
  ensures stk::R<a-n>;

int foo(int n) 
  requires stk::R<3>
  ensures stk::R<2> & res=n;
{
  check_stk(2);
  check_stk(3);
  //check_stk(x,4);
  subtr_stk(1);
  return n;
}
