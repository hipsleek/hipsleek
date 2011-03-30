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


node reverse(ref node xs, node ys,int z)
  requires xs::sll1<S1> * ys::rsll1<S2> & 
  forall(x: (x notin S1 | x>=z & forall (y:(y notin S2 | x>=y))))
  ensures res::rsll1<S> & S = union(S1, S2);//ys'::rsll1<S> // & S = union(S1, S2); //STRAND can not express S = S1 + S2
{
	if (xs != null) {
		node tmp;
		tmp = xs.next;
    //dprint;
		xs.next = ys;
		ys = xs;
    //dprint;
		return reverse(tmp, ys,z);

	} else return ys;
}

void reverse1(ref node xs, ref node ys,int z)
  requires xs::sll1<S1> * ys::rsll1<S2> & 
    forall(x: (x notin S1 | x>=z & forall (y:(y notin S2 | x>=y))))
  ensures ys'::rsll1<S> & S = union(S1, S2);//ys'::rsll1<S> // & S = union(S1, S2); //STRAND can not express S = S1 + S2
{
	if (xs != null) {
		node tmp;
		tmp = xs.next;
    //dprint;
		xs.next = ys;
		ys = xs;
    //dprint;
		reverse1(tmp, ys,z);

	} //else return ys;
}





