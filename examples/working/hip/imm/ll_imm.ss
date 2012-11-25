/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}

/* view for a singly linked list */

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;


lseg<p, n> == self=p & n=0
	or self::node<_, q> * q::lseg<p, n-1>
	inv n>=0;

int length (node x) 
requires x::ll<nn>@L
ensures res = nn;
//requires x::ll<n>
//ensures x::ll<n> & res = n;
{
 if (x==null) return 0;
    else 
      {
        //dprint;
        //x.val = 0;
        int r = 1+length(x.next);
        //dprint;
        return r;
      }
}

void append(node x, node y)
//  requires x::ll<n1> * y::ll<n2>@I & n1>0 
//  fails for requires x::ll<n1>@I * y::ll<n2>@I & n1>0 
//  ensures x::ll<n1+n2>@I;
  requires x::lseg<p,n>@L * p::node<v,null>
  ensures p::node<v,y>;
{
	if (x.next == null)
	      x.next = y;
	else 
		append(x.next, y);
}

/* return the tail of a singly linked list */
node get_next(node x)
	//requires x::ll<n> & n > 0
        //ensures x::ll<1> * res::ll<n-1>; 
	requires x::node<_, p> * p::ll<n1>@I
        ensures x::ll<1> * res::ll<n1>@I; 
{
  //dprint;
	node tmp = x.next;
	x.next = null;
	return tmp;
}

/* function to set the tail of a list */
 void set_next(node x, node y)

	requires x::ll<i> * y::ll<j>@I & i > 0 
	ensures x::ll<j+1>@I; 

{
	x.next = y;
}


/* function to get the third element of a list */
node get_next_next(node x) 

	//requires x::ll<n>@I & n > 1
	//ensures res::ll<n-2>@I;
	//requires x::node<_,q>@I*q::node<_,r>@I //ll<n>@I & n > 1
	//ensures res=r;
	requires x::lseg<r,2>@I
	ensures res=r;

{
	return x.next.next;
}



/* usage of & */
int sumN(node x, node y)
requires (x::node<a, _>@L & y::node<b, _>@L) 
ensures res=a+b;
{ return x.val + y.val; dprint;}

