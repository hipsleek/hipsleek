
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
    variance (1) [n1]
	ensures x::ll<n1+1>;

{
    node tmp = null;

	if (x.next == null)
		x.next = new node(a, tmp);
	else 
		insert_rec(x.next, a);
} 

void delete_last_rec(node x)
	requires x::ll<n1> & n1 > 1
    variance (1) [n1]
	ensures x::ll<n1-1>;
{
    if (x.next.next == null)
		x.next = x.next.next;
	else
	{
		delete_last_rec(x.next);
	}	
}

void insert(int a)
	requires p::ll<n> & n > 0
	ensures p'::ll<n'> & n'=n+1 & p=p';
        // read p
{
	insert_rec(p,a);
	n = n+1;
}

void delete_last()
	requires p::ll<n> & n > 1
	ensures p'::ll<n'> & n=n'+1 & p=p';
        // writes n; read p
{
	delete_last_rec(p);
	n = n-1;
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
	insert(2);
	insert(1);
	delete_last();
	delete_last();
}
