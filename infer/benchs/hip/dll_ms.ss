/* doubly linked lists */

/* representation of a node */
data node2 {
  int val; 
  node2 prev;
  node2 next;	
}

/* view for a doubly linked list without size */
dll<p> == self = null
  or self::node2<_ ,p , q> * q::dll<self> // = q1 
  inv true;



void insert(node2 x, int a)
  infer [x]
  requires x::dll<p> //&  x!=null  
  ensures x::dll<p>; 
{
  if (x.next == null)
    x.next = new node2(a, x, null);
  else 
    insert(x.next, a);
}


/* append 2 doubly linked lists */
void append2(node2 x, node2 y)
  infer [x]
	requires x::dll<q> * y::dll<p> // x!=null
	ensures x::dll<q>;
{
	node2 tmp;
	if (x.next == null) {
		x.next = y;
		if (y != null) {
			y.prev = x;
		}		
	}
	else {
		append2(x.next, y);
	}
}

/*
dlseg<sf, lf, sb, lb, n> == self=sf & n=0
			or self::node2<_, sf, r> * r::dlseg<self, lf, self, 

dlseg<p, q, n> == self=q & n=0
			or	self::node2<_, p, r> * r::dlseg<self, q, n-1>
			inv n>=0;
*/

/*
node2 append3(node2 x, node2 y)

	requires x::dll<q, m> * y::dll<p, n>
	ensures res::dll<_, m+n>;

{
	if (x == null)
		return y;
	else { 	
		node2 tmp = find_last(x);
		tmp.next = y;
		return x;
	}
}
*/

/*
node2 find_last(node2 x)
	requires x::dll<q, m> & m>0
	ensures res::node2<_,p,null> * x::dlseg<q, res, m-1>;
{
	if (x.next == null) return x;
	else return find_last(x.next);
}
*/

/*
void id1(node2 x, node2 y)
	requires x::dlseg<q, y, n> * y::node2<_,
*/
