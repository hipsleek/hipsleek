data node {
  int val;
  node next;
}

ll<n> == self=null & n=0
  or self::node<_,q> * q::ll<n-1>
  inv n>=0;

pred_prim RS<high:int>
  inv high>=0;

global RS stk;

void check_stk(int n)
  requires stk::RS<a>@L & a>=n
  ensures true;

// subtract space from stack
void sub_stk(int n)
  requires stk::RS<a> & a>=n
  ensures stk::RS<a-n>;

// add back space into stack
void add_stk(int n)
  requires stk::RS<a>
  ensures stk::RS<a+n>;

int length(node l) 
  requires stk::RS<m> * l::ll<n>@L & m=2*n+2 
  ensures  stk::RS<m> & res=n;
{
  sub_stk(2); //subtract stack frame
  int r;
  if (l==null) r=0;
  else r=1+length(l.next);
  add_stk(2); //add back stack frame prior to return
  return r;
}

