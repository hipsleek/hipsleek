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

//global RS_bnd stk_mark;
global RS stk;
global RS_mark mx;

// add back space into stack
void add_stk(int n)
  requires stk::RS<a> & n>=0
  ensures stk::RS<m> * mx::RS_mark<m> & m=a+n;

void sub_stk(int n)
  requires stk::RS<a> & n>=0 & a>=n
  ensures stk::RS<a-n>;

lemma "combine2" self::RS_mark<m1>*self::RS_mark<m2> 
  -> self::RS_mark<m> & m=max(m1,m2);

bool rand()
 requires true
 ensures res or !res;

relation R1(int n, int m).
relation R2(int n, int m).

int length(node l)
  infer [R1]
  requires l::ll<n>@L 
  ensures R1(res,n);
{
  int r;
  if (l==null) r=0;
  else r=1+length(l.next);
  return r;
}

