/* circular lists */

/* representation of a node */
data node {
	int val; 
	node next;	
}

/* view for singly linked circular lists */
cll<p, n> == self = p & n = 0
	or self::node<_, r> * r::cll<p, n-1> & self != p  
	inv n >= 0;

hd<n> == self = null & n = 0
	or self::node<_, r> * r::cll<self, n-1>  
	inv n >= 0;


relation A(int x, int y).
relation B(node x, node y). // can i have?

void insert(node x, int v)
	infer @pre[n,A]
	requires x::hd<n> //& n > 0 
	ensures x::hd<m> & A(m,n);
{
	node tmp;

	tmp = new node(v, x.next);
    //dprint;
	x.next = tmp;
	//dprint;
	//assert x'::hd<m>;
	//assume false;
}



/* functions to count the number of nodes in a circular list */
int count_rest(node rest, node h)
    infer @pre[A]
    requires rest::cll<p, n> & h = p 
    ensures rest::cll<p, n> & A(res,n); //res = n; 

{
	int n;
	
	if (rest == h)
		return 0; 
	else
	{
		n = count_rest(rest.next, h);
		n = n + 1;

		return n;
	}
}

int count(node x)
	infer @pre[A]
	requires x::hd<n>
	ensures x::hd<n> & A(res,n); //res = n; 
	
{
	int n;

	if (x == null)
		return 0;
	else 
	{
		n = count_rest(x.next, x);
		n = n + 1;

		return n;
	}
}


/* function to delete the node after the head in a circular list */
void delete(ref node x)
        infer @pre[n]
	requires x::hd<n> & n > 0
	ensures x'::hd<n-1>;

{
	node tmp;

	if (x.next == x)
		x = null;
	else
	{
		tmp = x.next.next;
		x.next = tmp;
	}
}

