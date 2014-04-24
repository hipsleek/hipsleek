data node{
	int val;
	node next;
}

//ll<> == self = null  or self::node<_, q> * q::ll<>;

//ltwo<p:node> == p::ll<> & self = null  or 
//   self::node<_, q> * p::node<_,r> * q::ltwo<r>;


HeapPred HL(node a).
HeapPred H(node a, node b).
HeapPred G(node a, node b).

ltwoB<p:node> == HL(p) & self = null  or 
   self::node<_, q> * p::node<_,r> * q::ltwoB<r>;

bool check_zip_eq (node x, node y)
//infer [H,G]  requires H(x,y)  ensures  G(x,y) & res;
requires x::ltwoB<y>@L  ensures res;
{
   if (x==null) return y==null;
   else return check_zip_eq(x.next,y.next);
}

/*

# check-zip-eq.ss



*/

