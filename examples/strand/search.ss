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


bool search(node x, int d)
 requires x::sll1<S> & d notin S
 ensures !res;
 requires x::sll1<S> & d in S
 ensures res;
{
	int tmp;

	if (x==null) return false;
	else
	{
      if (x.val == d) return true;
      else return search(x.next,d);
	}
}

node search1(node x, int d)
  requires x::sll1<S> & d in S
  ensures res::node<d,_>;
  requires x::sll1<S> & d notin S
  ensures x::sll1<S> & res=null;


/*
  requires x::sll1<S>@I & d in S
  ensures res::node<d,_>@I;
  requires x::sll1<S>@I & d notin S
  ensures res=null;
  requires x::sll1<S> & d in S
  ensures res::node<d,_>;
  requires x::sll1<S> & d notin S
  ensures x::sll1<S> & res=null;
*/
{


	if (x==null) return x;
	else
	{
      if (x.val == d) return x;
      else if (x.val>d) return null;
      else return search1(x.next,d);
	}
    //return null;
}












