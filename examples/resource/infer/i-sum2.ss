
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

int sum(int x)
  infer [R1]
  requires stk::RS<m> & x>=0
  ensures  stk::RS<m> * mx::RS_mark<h> & res=2*x
   & R1(h,m,x);
  //& h=m+1*x+1;
{
  add_stk(2); //subtract stack frame
  int r;
  if (x==0) {
     r=0;
  }
  else {
    r=2+sum(x-1);
  }
  sub_stk(2); //add back stack frame prior to return
  return r;
}

