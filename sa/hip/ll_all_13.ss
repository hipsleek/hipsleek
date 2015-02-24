/* singly linked lists */

/* representation of a node */

data node {
	int val; 
	node next;	
}


/* view for a singly linked list */

ll<n> == self = null & n = 0 
	or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

ls<> == self = null  
	or self::node<_, q> * q::ls<> 
  inv true;


HeapPred H(node a).
HeapPred H1(node a).
HeapPred H2(node a, node b).
HeapPred H3(node a, node b, node c).
HeapPred G(node a, node b).
HeapPred G1(node a).
HeapPred G2(node a, node b).
HeapPred G3(node a, node b, node c).


node delete1(node x, int a)

  requires x::ls<>
  ensures res::ls<>;

     infer [H1,G2]
     requires H1(x)
     ensures G2(x,res);
/*

[ H1(x_618) ::= emp&x_618=null,
 G2(x_619,v_node_33_620) ::= 
 x_619::node<v_int_35_601,next_35_589> * G2(next_35_589,v_node_36_616) * 
 v_node_33_620::node<v_int_35_601,v_node_36_616>&true
 or emp&x_619=null

The above result is wrong. It may be quite 
tricky to infer but I would be expecting
which is equivalent to:
  requires x::ls<>
  ensures res::ls<>;

   H1(x) = x=null
    or x::node<_,q>*H1(x)
   G2(x,res) = res=null
    or res::node<_,q>* G2(_,q)


*/
{
	if (x == null) 
		return x;
	else {
		if (x.val == a) return x.next;
		else return new node(x.val, delete1(x.next, a));
	}
}

/*

node create_list(int a)
	requires a >= 0 
	ensures res::ll<a>;

{
	node tmp;

	if (a == 0) {
      // assume false;
		return null;
	}
	else {    
		a  = a - 1;
        //    dprint;
		tmp = create_list(a);
        //    dprint;
		return new node (0, tmp);
	}
		
}

void reverse(ref node xs, ref node ys)
	requires xs::ll<n> * ys::ll<m> 
	ensures ys'::ll<n+m> & xs' = null;
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
*/
/*
void reverse1(ref node xs, ref node ys)
	requires xs::ll1<S1> * ys::ll1<S2> 
	ensures ys'::ll1<S3> & S3 = union(S1, S2) & xs' = null;
{
	if (xs != null) {
		node tmp;
		tmp = xs.next;
		xs.next = ys;
		ys = xs;
		xs = tmp;
		reverse1(xs, ys);
	}
}*/
/*
void test(node x)
	requires x::ll<n> & n>=2 ensures x::ll<n-1>;
{
	node tmp = x.next.next;
	x.next = tmp;
}
*/




