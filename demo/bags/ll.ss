/* singly linked lists */

/* representation of a node */
data node {
	int val; 
	node next;	
}

/* view for a singly linked list */



ll<S> == self = null & S = {} 
	or self::node<v, q> * q::ll<S1> & S = union(S1, {v});

	
/*ll2<n, S> == self=null & n=0 & S={}
	or self::node<v, r> * r::ll2<m, S1> & n=m+1 & S=union(S1, {v});*/

/* append two singly linked lists */
void append(node x, node y)
	requires x::ll<S1> * y::ll<S2> & x != null
	ensures x::ll<S> & S = union(S1, S2);

{
	if (x.next==null)
    {      
      x.next = y;
      //dprint;
      //assume false;
    }
	else
   {
    //assume false;
		append(x.next, y);
    }
}

/* function to insert a node in a singly linked list */
void insert(node x, int a)
	requires x::ll<S> & S != {}
	ensures x::ll<S1> & S1 = union(S, {a});

{
        node tmp = null;

	if (x.next == null)
		x.next = new node(a, tmp);
	else 
		insert(x.next, a);
} 

/* function to delete the a-th node in a singly linked list */
node delete1(node x, int a)
	requires x::ll<S>  
	ensures res::ll<S1> & (a notin S & S = S1 | S=union(S1, {a}));
{
	if (x == null) 
		return x;
	else {
		if (x.val == a) return x.next;
		else return new node(x.val, delete1(x.next, a));
	}
}

/* function to reverse a singly linked list */
void reverse1(ref node xs, ref node ys)
	requires xs::ll<S1> * ys::ll<S2> 
	ensures ys'::ll<S3> & S3 = union(S1, S2) & xs' = null;
{
	if (xs != null) {
		node tmp;
		tmp = xs.next;
		xs.next = ys;
		ys = xs;
		xs = tmp;
		reverse1(xs, ys);
	}
}
