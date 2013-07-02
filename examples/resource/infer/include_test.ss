data node {
  int val;
  node next;
}

ll<n> == self=null & n=0
  or self::node<_,q> * q::ll<n-1>
  inv n>=0;
//global RS_bnd stk_mark;

pred_prim RS<high:int>
  inv high>=0;

pred_prim RS_mark<high:int>
  inv 0<=high;

lemma "combine2" self::RS_mark<m1>*self::RS_mark<m2> 
  -> self::RS_mark<m> & m=max(m1,m2);

int bach()
requires true
ensures res=2;
//{
// return 1;
//}


global RS stk;
global RS_mark mx;
// add back space into stack

void add_stk(int n)
  requires stk::RS<a> & n>=0
  ensures stk::RS<m> * mx::RS_mark<m> & m=a+n;

void sub_stk(int n)
  requires stk::RS<a> & n>=0 & a>=n
  ensures stk::RS<a-n>;

