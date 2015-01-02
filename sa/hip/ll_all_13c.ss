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

ls2<> == self = null  
	or self::node<_, q> * q::ls2<> 
  inv true;
/*
ls1<> == self = null
	or self::node<_, q> * q::ls1<>
  or self::node<_, q> & q = null
  inv true;
*/

HeapPred H(node a).
HeapPred H1(node a).
HeapPred H2(node a, node b).
HeapPred H3(node a, node b, node c).
HeapPred G(node a, node b).
HeapPred G1(node a).
HeapPred G2(node a, node b).
HeapPred G3(node a, node b, node c).


node trav(node x)
     infer [H1,G1]
     requires H1(x)
     ensures G1(res);

  /* requires x::ls2<> */
  /* ensures res::ls2<>; */
/*

You obtained below which is good.

    bool b = rand();
	if (b) return x.next;
    // H1(x) --> x::node<val_53_555',next_53_556'> * HP_577(next_53_556')
    // HP_577(v_node_53_557') --> G1(v_node_53_557'),
	else {
    // H1(x) --> x::node<val_55_558',next_55_559'> * HP_582(next_55_559')
      x.next = trav(x.next);
    // HP_582(v_node_55_560') --> H1(v_node_55_560'),
      return x;
//G1(v_node_55_605) * x::node<val_55_588,v_node_55_605>&
//  v_node_56_564'=x --> G1(v_node_56_564')&true,

NORMALIZATION
=============
From:
    // H1(x) --> x::node<val_53_555',next_53_556'> * HP_577(next_53_556')
    // H1(x) --> x::node<val_55_558',next_55_559'> * HP_582(next_55_559')
Deduce HP_577 = HP_582

From:
    // HP_582(v_node_55_560') --> H1(v_node_55_560'),
Deduce HP_582 = H1

Hence: H1(x) --> x::node<_,q>*H1(q)

From:
// H1(v_node_53_557') --> G1(v_node_53_557'),
//G1(v_node_55_605) * x::node<val_55_588,v_node_55_605>&
//  v_node_56_564'=x --> G1(v_node_56_564'),

Deduce:
  G1(res) <- H1(res)
  G1(res) <- res::node<_,q>*G1(q)
  H1(x) -> x::node<_,q>*H1(q)

Thus:
  H1(x)   <-> x::node<_,q>*H1(q)
  G1(res) <-> H1(res)

*/
{
    bool b = rand();
	if (b) return x.next;
	else {
      x.next = trav(x.next);
      return x;
    }
}

bool rand() 
  requires true
  ensures res or !res; 

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




