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

rsll1<S> == self = null & S = {}
	or self::node<v2, r> * r::rsll1<S1> & S = union(S1, {v2}) & 
	forall(x: (x notin S1 | v2 >= x));


void reverse(ref node xs, ref node ys)
	requires xs::sll1<S1> * ys::sll1<S2>
  ensures true;//ys'::rsll1<S> & xs' = null;// & S = union(S1, S2); //STRAND can not express S = S1 + S2
{
	if (xs != null) {
		node tmp;
		tmp = xs.next;
    //dprint;
		xs.next = ys;
		ys = xs;
		xs = tmp;
    //dprint;
		reverse(xs, ys);
	}
}




