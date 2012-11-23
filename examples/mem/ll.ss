/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}

global int heap;
global int stk;

/* view for a singly linked list */
ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

// r denotes the allocated heap size of the data structure
// n denotes the length of list
pll<n,r> == self = null & n = 0 & r=0
  or self::node<_, q> * q::pll<n-1,r-2>  
  inv n >= 0 & r>=0 ; // & r=2*n;

// r denotes the allocated heap size of the data structure.
rll<r> == self = null & r=0
  or self::node<_, q> * q::rll<r-2>  
  inv r>=0;

node newnode(int x, node n)
  requires heap>=2
  ensures "heap":res::node<x,n> & heap'=heap-2; //'
{

  heap = heap-2; // instrumentation
  assert "heap":heap'>=0; //'
  return new node(x,n);
}

void dispose(node x)
  requires x::node<_,_>
  ensures  "heap":heap'=heap+2; //'
{

  heap = heap+2; // instrumentation
}

node new_list(int n)
  requires heap>=2*n & n>=0 & stk>=4*n+4
  ensures "stack": res::ll<n> & heap'=heap-(2*n) & stk'=stk; 
  requires heap>=2*n & n>=0
  ensures res::pll<n,2*n> & heap'=heap-2*n; //'
  requires heap>=2*n & n>=0
  ensures res::rll<r> & heap'=heap-r & r=2*n; //'
{ stk = stk-4;
  assert "stack": stk'>=0;//'
  node r= null;
  if (n>0) {
    r = new_list(n-1,stk);
    r = newnode(n,r);
    }
  stk = stk+4;
 return r;
}

node twice_list(node x)
  requires x::ll<n> & heap>=4*n & stk>=4*n+4 
  ensures "stack":res::ll<2*n>*x::ll<n> & heap'=heap-(4*n) & stk'=stk; //'
  requires x::rll<r> & heap>=2*r 
  ensures res::rll<2*r>*x::rll<r> & heap'=heap-2*r; //'
{ 
  stk = stk-4;
  assert "stack":stk'>=0; //'
  node r = null;
  if (x!=null) {
    r = twice_list(x.next);
    r = newnode(x.val,r);
    r = newnode(x.val,r);
  }
  stk = stk+4;
  return r;
}

void del_list(node x)
  requires x::ll<n> & stk>=3*n+3
  ensures "stack":heap'=heap+(2*n) & stk'=stk; //'
  requires x::pll<n,r>
  ensures heap'=heap+r; //'
  requires x::rll<r>
  ensures heap'=heap+r; //'
{ 
  stk = stk-3;
  assert "stack":stk'>=0; //'
  if (x!=null) {
    del_list(x.next);
    dispose(x);
  }
  stk = stk+3;
}

void tgt(int n)
  requires n>=0 & heap>=2*n & stk>=4*(n+1)+3
  ensures "stack":heap'=heap & stk'=stk; //'
{
  stk = stk-3;
  assert "stack": stk'>=0; //'
  node x=new_list(n);
  del_list(x);
  stk = stk+3;
}




