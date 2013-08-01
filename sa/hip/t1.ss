
data node {
	int val;
	node next;
}

ll<n> == self=null & n=0
	or self::node<_, q> * q::ll<n-1>
	inv n>=0;

// single conditional
// is disjunct in Octx or [OCtx]? 


int foo(int N) 
 requires true
  ensures res=N;
{
int i = 0;
while (i < N) 
  requires true
  ensures i'=N;
  {
    i = i+1;
  }
 return i;
}

node f(int x)
requires true
ensures res::ll<1> & x>0
    or res::ll<2> & x<=0;
/*
case {
 x>0 -> ensures res::ll<1>;
 x<=0 -> ensures res::ll<2>;
 }
*/
{
 node y;
 y = null;
 if (x>0) {
y.val=0;
        y=new node(1,null);
 }
 else {
    y=new node(5,new node(6,null));
 };
 dprint;
return y;
}
