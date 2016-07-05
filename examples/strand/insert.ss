/* selection sort */

data node {
	int val; 
	node next; 
}

ll1<S> == self = null & S = {}
	or self::node<v2, r>* r::ll1<S1> & S = union(S1, {v2});

sll1<S> == self = null & S = {}
	or self::node<v2, r> * r::sll1<S1> & S = union(S1, {v2}) & 
	forall(x: (x notin S1 | v2 <= x));

/*
node insert(node x, int k)
    requires x::sll1<S> & k notin S
  ensures  x::sll1<S1> & S1 = union(S, {k});

{
  if (x == null){
    return new node (k, null);
  }
  else{
    if (k <= x.val){
     return new node (k, x);
	}
	else{
       if (x.next == null){
         node y = new node (k, null);
         x.next = y;
         return x;
       }
       else{
         return insert(x.next, k);
       }
	}
  }
}
*/

node insert(node x, int v)
	requires x::sll1<S>
	ensures res::sll1<S1> & S1 = union(S, {v}); 

{
	node tmp;
        node tmp_null = null;

	if (x == null)
		return new node(v, tmp_null);
	else
	{
		if (v <= x.val)
			return new node(v, x);
		else
		{
			tmp = x.next;
			x.next = insert(tmp, v);	
			return x;
		}
	}
}







