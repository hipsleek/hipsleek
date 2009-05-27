data node {
	int val;
	node next;
}

ll<n> == self=null & n=0
	or self::node<_, q> * q::ll<n-1>
	inv n>=0;

lseg<p, n> == self=p & n=0
	or self::node<_, q> * q::lseg<p, n-1>
	inv n>=0;

clist<n> == self::node<_,p> * p::lseg<self,n-1>
	inv n>=1;

void append(node x, node y)
	requires x::ll<n> & n>0
	ensures x::lseg<y, n>;
	requires x::ll<n> & y=x & n>0
	ensures x::clist<n>;
{
	node tmp = x.next;
	bool fl = tmp != null;
	if (fl) {
		append(x.next, y);
		return;
	}
	else {
		x.next = y;
		return;
	}
}

int test(int x)
/*
  case {
   x>0 -> ensures res=1;
   x<=0 -> ensures res=3;
  }
*/
requires true
  ensures x>0 & res=1 
     or x<=0 & res=2;
{
 if (x>0) {return 1;}
 else {
   assert x>0;
   assert x<=1;
   if (x>2) 
     {return 2;}
   else 
     {return 3;}
 }
}     
