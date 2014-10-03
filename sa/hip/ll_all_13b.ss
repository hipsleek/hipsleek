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


void trav(node x)

     infer [H1,G1]
     requires H1(x)
     ensures G1(x);
     /* requires x::ls2<> */
     /* ensures x::ls2<>; */

/*
  requires x::ls<>
  ensures x::ls<>;

PROBLEM : Simpler than 13a..

[ G1(x_593) ::= x_593::ls[LHSCase]&true,
 H1(x_591) ::= 
 x_591::node<val_83_555',next_83_556'>&next_83_556'=null
 or emp&x_591=null
 or x_591::ls[LHSCase]&true
 or x_591::node<val_83_555',next_83_556'> * H1(next_83_556')&true
 ]

 G1(x) ::= x::ls<>
 H1(x) :: x::ls<>

**

//H1(x)
	if (x == null) 
// RELASS [H1,G1]H1(x)&x=null --> G1(x)&true,
		return;
	else {
        bool b = rand();
		if (b) return;
        //RELASS [H1,G1]H1(x)&x!=null --> G1(x)&true,
		else trav(x.next);
 // [H1,HP_575]H1(x)&x!=null --> x::node<val_68_555',next_68_556'> 
 //   * HP_575(next_68_556')&true]
// pre : [HP_575,H1]HP_575(v_node_68_557')&true --> H1(v_node_68_557')&true,
// [G1]x::node<val_68_581,v_node_68_586> * G1(v_node_68_586)&
// --> G1(x)&true,
	}


*/
{
	if (x == null) 
		return;
	else {
        bool b = rand();
		if (b) return;
		else trav(x.next);
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




