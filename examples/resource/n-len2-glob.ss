data node {
  int val;
  node next;
}

ll<n> == self=null & n=0
  or self::node<_,q> * q::ll<n-1>
  inv n>=0;

pred_prim RS<high:int>
  inv high>=0;
pred_prim RS_mark<high:int>
  inv 0<=high;

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


int length(node l) 
  requires stk::RS<m> * l::ll<n>@L  
  ensures  stk::RS<m> * mx::RS_mark<h> & h=m+2*n+2 & res=n;
{
  add_stk(2); //increase stack frame
  int r;
  if (l==null) r=0;
  else r=1+length(l.next);
  sub_stk(2); //decrease stack frame prior to return
  return r;
}

int len_tail(node l,int a) 
  requires stk::RS<m> * l::ll<n>@L 
  ensures  stk::RS<m> * mx::RS_mark<h> & h=m+2 & res=n+a;
{
  add_stk(2); //increase stack frame
  int r;
  if (l==null) {
      sub_stk(2); //decrease stack frame
      r=a;
  }
  else {
     a=a+1;
     node q = l.next;
     sub_stk(2); //decrease stack frame for last operation;
     r=len_tail(q,a);
  };
  return r;
}
