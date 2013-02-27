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

bool rand()
 requires true
 ensures res or !res;

int g() 
  requires stk::RS<m> & true
  ensures  stk::RS<m> * mx::RS_mark<h>  & res=1
  & h=m+1
  ;
{
  add_stk(1);
  int r;
  r=1;
  sub_stk(1);
  return r;
}


int h() 
  requires stk::RS<m> 
  ensures  stk::RS<m> * mx::RS_mark<h> & h=m+2 & res=2;
{
  add_stk(1);
  int r;
  int x=g();
  r=x+1;
  sub_stk(1);
  return r;
}


int f() 
  requires stk::RS<m> 
  ensures  stk::RS<m> * mx::RS_mark<h> & h=m+3 & res=3;
{

  add_stk(1);
  int r=g();
  r = r+h();
  sub_stk(1);
  return r;
}


