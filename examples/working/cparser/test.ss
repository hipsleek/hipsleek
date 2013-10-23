
data node {
	int val; 
	node next;	
}

global int n;
global node p;

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n1> & n = n1 + 1
	inv n >= 0;

void insert_rec(node x, int a)
	requires x::ll<n1> & n1 > 0 
	ensures x::ll<n1+1>;

{
    node tmp = null;

	if (x.next == null)
		x.next = new node(1, tmp);
	else 
		insert_rec(x.next, 1);
} 

void insert(int a)
	requires p::ll<n> & n > 0
	ensures p'::ll<n'> & n'=n+1 & p=p';
        // read p
{
	insert_rec(p,1);
	n = n+1;
}

void main()
	requires true
    ensures p'::ll<n'> & n'=3;
        // writes n,p
{
	p = new node(5,null);
    n=1;  // I added this
 // dprint;
	insert(4);
	insert(3);
}
