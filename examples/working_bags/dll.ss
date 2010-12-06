/* doubly linked lists */

/* representation of a node */
data node2 {
	int val; 
	node2 prev;
	node2 next;	
}

/* view for a doubly linked list with bag of values */
dll1<p,S> == self = null & S = {} 
	or (exists q1: self::node2<v ,p , q> * q::dll1<q1, S1> & S = union(S1, {v}) & self = q1); 

void insert(node2 x, int a)
	requires x::dll1<p, S> & S != {} 
	ensures x::dll1<p, S1> & S1 = union(S, {a}); 
{
	node2 tmp_null = null;

		if (x.next == null) {
      x.next = new node2(a, x, tmp_null);
		}
		else {
			insert(x.next, a);
		}
}


node2 append(node2 x, node2 y) // for this I got the Mona + Isabelle timings
	requires x::dll1<q, S1> * y::dll1<p, S2>
	ensures res::dll1<_, S> & S = union(S1, S2);
{
	node2 tmp;

	if (x == null)
  {
    assume false;
		return y;
	}else
	{ 	
		tmp = append(x.next, y);
    x.next = tmp;
    if (tmp != null)		
    {  tmp.prev = x;
       dprint;
    }
    else assume false;
		return x; 
	}
}
