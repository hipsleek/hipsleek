pred_prim R<high:int>
  inv high>=0;

lemma "R split" self::R<b> & q,r>=0 & b=q+r <-> self::R<q> * self::R<r> ;

global R stk;

void check_rs(int n)
  requires stk::R<a>@L & a>=n
  ensures true;

// subtract space from stack
void sub_RS(int n)
  requires stk::R<a> & a>=n
  ensures stk::R<a-n>;

// add back space into stack
void add_RS(int n)
  requires stk::R<a>
  ensures stk::R<a+n>;

void f() 
  requires stk::R<m> & m=6
  ensures  stk::R<m>;
{
  sub_RS(2); //subtract stack frame
  //dprint;
  g();
  add_RS(2); //add back stack frame prior to return
}

void g() 
  requires stk::R<m> & m=2
  ensures  stk::R<m>;
{
  sub_RS(2); //subtract stack frame
  add_RS(2); //add back stack frame prior to return
}
