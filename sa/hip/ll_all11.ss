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


void insert(node x, int a)
    infer [H1,G1]
	requires H1(x)
     ensures G1(x);
     /*
[ HP_615(next_34_549') ::= 
 emp&next_34_549'=null
 or next_34_549'::node<val_34_548',next_34_618> * HP_615(next_34_618)&true
 ,
 HP_609(v_node_35_602) ::= 
 v_node_35_602::node<a,tmp_23'>&tmp_23'=null
 or v_node_35_602::node<val_34_575,v_node_35_612> * HP_609(v_node_35_612)&
    true
 ,

 H1(x_614) ::= x_614::node<val_34_548',next_34_549'> * HP_615(next_34_549')&true,
 G1(x_608) ::= x_608::node<val_34_575,v_node_35_602> * HP_609(v_node_35_602)&true]

PROBLEM:
 Can improve to
 HP_609(v) = v::node<_,q>*HP_615(q)

      */
{
			//dprint;
      node tmp = null;
	if (x.next == null)
		x.next = new node(a, tmp);
	else 
		insert(x.next, a);
} 

/*

void delete(node x, int a)
	requires x::ll<n> & n > a & a > 0 
	ensures x::ll<n - 1>;
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




