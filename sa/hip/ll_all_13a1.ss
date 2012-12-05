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


node delete_mid(node x)
 infer [H1,G2]
 requires H1(x)
 ensures G2(x,res);
/*
  requires x::ls<>
  ensures res::ls<>;

 [ RELASS [G2,HP_599]
  G2(q_597,v_node_81_595) * 
  v_node_81_560'::node<v_596,v_node_81_595> * x::node<v_596,q_597>&
  true --> G2(x,v_node_81_560') 
      * HP_599(q_597,v_node_81_595,v_node_81_560')  true,

 // ERROR : where did HP_599 came from?

 RELASS [HP_579,G2]HP_579(v_node_80_558') * x::node<v_589,v_node_80_558'>&
  true --> G2(x,v_node_80_558')&true,
 RELASS [H1,G2]H1(x)&x=null & v_node_76_557'=null --> G2(x,v_node_76_557')&
  true,
 RELASS [HP_580,H1]HP_580(q_27')&true --> H1(q_27')&true,
 RELASS [H1,HP_580]H1(x)&x!=null --> x::node<v_26',q_27'> * HP_580(q_27')&
  true,
 RELASS [H1,HP_579]H1(x)&x!=null --> x::node<v_26',q_27'> * HP_579(q_27')&
  true]


	if (x == null) 
		return x;
   //H1(x)&x=null & v_node_76_557'=null --> G2(x,v_node_76_557')&true,
	else {
        bool b = rand();
  //H1(x)&x!=null --> x::node<v_26',q_27'> * HP_580(q_27')& true,
  //H1(x)&x!=null --> x::node<v_26',q_27'> * HP_579(q_27')&true
  // due to disjunctive state ..

        bind x to (v,q) in {
		  if (b) return q;
          // HP_579(v_node_80_558') * x::node<v_589,v_node_80_558'>&true 
             --> G2(x,v_node_80_558')&true,

		  else return new node(v, delete_mid(q));
          // HP_580(q_27')&true --> H1(q_27')&true,
  // G2(q_597,v_node_81_595) * v_node_81_560'::node<v_596,v_node_81_595> 
  // * x::node<v_596,q_597>&true 
  // --> G2(x,v_node_81_560') 
  //      * HP_599(q_597,v_node_81_595,v_node_81_560') & true,

        }
	}


*/
{
	if (x == null) 
		return x;
	else {
        bool b = rand();
        bind x to (v,q) in {
		  if (b) return q;
		  else return new node(v, delete_mid(q));
        }
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




