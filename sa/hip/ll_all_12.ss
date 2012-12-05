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

HeapPred H(node a).
HeapPred H1(node a).
HeapPred H2(node a, node b).
HeapPred H3(node a, node b, node c).
HeapPred G(node a, node b).
HeapPred G1(node a).
HeapPred G2(node a, node b).
HeapPred G3(node a, node b, node c).



void delete(node x, int a)
     infer [H1,G1]
     requires H1(x)
     ensures G1(x);
/*
[ HP_626(v_node_37_619) ::=UNKNOWN,
 HP_587(next_37_552') ::=UNKNOWN,
 HP_695(v_node_37_619) ::= 
 HP_626(v_node_37_619)&true
 or v_node_37_619::node<val_37_586,v_node_37_698> * HP_695(v_node_37_698)&
    true
 ,
 HP_680(next_37_549') ::= 
 next_37_666::node<val_37_551',next_37_671> * HP_587(next_37_671) * 
 next_37_549'::node<val_37_551',next_37_666>&true
 or next_37_674::node<val_37_551',next_37_673> * HP_587(next_37_673) * 
    next_37_666::node<val_37_628,next_37_674> * 
    next_37_549'::node<val_37_551',next_37_666>&true
 or next_37_549'::node<val_37_551',next_37_666> * HP_587(next_37_666)&true
 or next_37_666::node<val_37_548',next_37_669> * 
    next_37_549'::node<val_37_551',next_37_666>&true
 or next_37_666::node<val_41_630,next_37_666> * 
    next_37_549'::node<val_37_551',next_37_666>&true
 or next_37_549'::node<val_37_548',next_37_691> * HP_680(next_37_691)&true
 ,
 H1(x_679) ::= x_679::node<val_37_548',next_37_549'> * HP_680(next_37_549')&true,
 G1(x_694) ::= x_694::node<val_37_586,v_node_37_619> * HP_695(v_node_37_619)&true]

** ERROR
This should be an example where shape analysis fail.
The fact that it succeeded points to a possible
unsoundness problem in our inference!
The only exception is when it is able to infer
a circular structure. Can we?

*/

{
        if (a == 1)
	{
		//node tmp = x.next.next;
		//x.next = tmp;
                  x.next = x.next.next;
	}
	else
	{
		delete(x.next, a-1);
	}	
}

/*
node delete1(node x, int a)
	requires x::ll1<S>  
	ensures res::ll1<S1> & ((a notin S | S=union(S1, {a})) | S = S1);
{
	if (x == null) 
		return x;
	else {
		if (x.val == a) return x.next;
		else return new node(x.val, delete1(x.next, a));
	}
}

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




