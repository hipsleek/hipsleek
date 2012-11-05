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

ls1<> == self = null
    or self::node<_, _>
	or self::node<_, q> * q::ls1<> 
  inv true;


HeapPred H(node a).
HeapPred H1(node a).
HeapPred H2(node a, node b).
HeapPred H3(node a, node b, node c).
HeapPred G(node a, node b).
HeapPred G1(node a).
HeapPred G2(node a, node b).
HeapPred G3(node a, node b, node c).


node delete_mid(node x)
 infer [H1,G2]
 requires H1(x)
 ensures G2(x,res);

/*
  requires x::ls<>
  ensures res::ls<>;

 RELASS [G2,HP_616]
  x::node<v_int_60_613,next_60_597> * 
  G2(next_60_597,v_node_60_614) * 
  v_node_60_566'::node<v_int_60_613,v_node_60_614>&
  true --> G2(x,v_node_60_566') * HP_616(v_node_60_614,v_node_60_566')&true,
 RELASS [HP_585,G2]
  HP_585(v_node_59_558') * 
  x::node<val_59_608,v_node_59_558'>&true 
  --> G2(x,v_node_59_558')&true,
 RELASS [H1,G2]H1(x)&x=null & v_node_56_555'=null --> G2(x,v_node_56_555')&
  true,
 RELASS [HP_590,H1]HP_590(next_60_597)&true --> H1(next_60_597)&true,
 RELASS [H1,HP_590]H1(x)&x!=null --> x::node<val_60_559',next_60_560'> * 
  HP_590(next_60_560')&true,
 RELASS [H1,HP_585]H1(x)&x!=null --> x::node<val_59_556',next_59_557'> * 
  HP_585(next_59_557')&true]

What happen to below?
   G2(x,res) = x::node<_,q> & res=q

Isn't this a possible case that is not captured below..

[ G2(x,res) ::= 
    x::node<v_int_81_613,next_81_597> * G2(next_81_597,v_node_81_614) * 
    res::node<v_int_81_613,v_node_81_614>&true
 or emp&x=null & res=null
 ,
 H1(x_631) ::= x_631::ls[LHSCase]&true]
* 
  
 H1(x) & x=null & res=x --> G1(x,res)
 H1(x) & x!=null 

*/
{
	if (x == null) 
		return x;
	else {
        bool b = rand();
		if (b) return x.next;
		else return new node(x.val, delete_mid(x.next));
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




