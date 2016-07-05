/* representation of a node */
data node {
	int val; 
	node next;	
}

/* view for a singly linked list */
ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1>
	inv n >= 0;

lnB<n,B> == self = null  & n = 0 & B = {}
	or self::node<v,q> * q::lnB<n-1,B1> & B = union(B1,{v})
	inv n >= 0;


int length(node x)
requires x::ll<n>
ensures x::ll<n> & res = n;
{
if (x == null) return 0;
else return (1+length(x.next));
}

void append(node x, node y)
requires x::lnB<n1,B1> * y::lnB<n2,B2> & x != null //& Term[n1]
ensures x::lnB<n1+n2,union(B1,B2)>;
{
if (x.next == null) x.next = y;
else append(x.next,y);
}

void append_s(node x, node y)
requires x::ll<n> * y::ll<m> & x != null
ensures x::ll<n+m>;
{
if (x.next == null) x.next = y;
else append_s(x.next,y);
}
