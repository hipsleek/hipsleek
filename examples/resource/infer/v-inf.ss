
pred_prim RS<high:int>
  inv high>=0;

pred_prim RS_mark<high:int>
  inv 0<=high;

//global RS_bnd stk_mark;
global RS stk;
global RS_mark mx;

// add back space into stack
void add_stk(int n)
  requires stk::RS<a> & n>=0
  //ensures stk::RS<m> & m=a+n;
  ensures stk::RS<m> * mx::RS_mark<m> & m=a+n;

void sub_stk(int n)
  requires stk::RS<a> & n>=0 & a>=n
  ensures stk::RS<a-n>;

lemma "combine2" self::RS_mark<m1>*self::RS_mark<m2> 
  -> self::RS_mark<m> & m=max(m1,m2);

relation R1(int h, int n, int m).
relation R2(int h, int n, int m).

int foo(int x)
  //infer [R1]
  requires stk::RS<m> & x>=0
  ensures  stk::RS<m> * mx::RS_mark<h> 
  //& R1(h,m,x);
  & false;
  //& \inf<=h;
{
  add_stk(1); //subtract stack frame
  int r;
  r = foo(x);
  sub_stk(1); //add back stack frame prior to return
  return r;
}

