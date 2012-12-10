/* circular lists */

/* representation of a node */
data node {
	int val; 
	node next;	
}

/* view for singly linked circular lists */
cll1<p, S> == self = p & S = {}
	or self::node<v, r> * r::cll1<p, S1> & S = union(S1, {v}) & self != p;

hd1<S> == self = null & S = {}
	or self::node<v, r> * r::cll1<self, S1> & S = union(S1, {v});  

cll2<p, n, S> == self = p & n = 0 & S = {}
	or self::node<v, r> * r::cll2<p, n1, S1> & n = n1+1 & S = union(S1, {v}) & self != p  
	inv n >= 0;

hd2<n, S> == self = null & n = 0 & S = {}
	or self::node<v, r> * r::cll2<self, n1, S1> & n = n1+1 & S = union(S1, {v})  
	inv n >= 0;


int count_rest(node x, node h)
	requires x::cll2<p, n, S> & h = p 
	ensures x::cll2<p, n, S> & res = n; 

{
	int n;
	
	if (x == h)
		return 0; 
	else
	{
		n = count_rest(x.next, h);
		n = n + 1;

		return n;
	}
}

int count(node x)	
	requires x::hd2<n, S>
	ensures x::hd2<n, S> & res = n; 
	
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
int delete(ref node x)
	requires x::hd1<S> & S != {}
	ensures x'::hd1<S1>;
{
	node tmp;

	if (x.next == x) {
			tmp = x;
			x = null;
			return tmp.val;
	}
	else{
		tmp = x.next;
		x.next = tmp.next;
		return tmp.val;
	}
}

int delete2(ref node x)
	requires x::hd2<n, S> & S != {} & n > 0
	ensures x'::hd2<n1, S1> & S = union(S1, {res}) & n = n1 + 1;
{

	node tmp;

	if (x.next == x) {
      tmp = x;
			x = null;
			return tmp.val;
	}
	else{
   tmp = x.next;
   x.next = tmp.next;
   int t=tmp.val;
   return t;
  }
}
