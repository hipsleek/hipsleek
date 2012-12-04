data node {
  int val;
  node next;
}

ll<n> == self=null & n=0
  or self::node<_,q> * q::ll<n-1>
  inv n>=0;

pred_prim stk2<high:int>
  inv high>=0;

void check_stk(stk2 x, int n)
  requires x::stk2<a>@L & a>=n
  ensures true;

// subtract space from stack
void subtr_stk(stk2 x, int n)
  requires x::stk2<a> & a>=n
  ensures x::stk2<a-n>;

// add back space into stack
void add_stk(stk2 x, int n)
  requires x::stk2<a>
  ensures x::stk2<a+n>;

int length(stk2 s,node l,int a) 
  requires s::stk2<m> * l::ll<n>@L & m>=2 
  ensures  s::stk2<m> & res=n+a;
{
  subtr_stk(s,2); //subtract stack frame
  int r;
  if (l==null) {
      add_stk(s,2); //add back stack frame
      r=a;
  }
  else {
     a=a+1;
     node q = l.next;
     add_stk(s,2); //add back stack frame for last operation;
     r=length(s,q,a);
  };
  return r;
}

