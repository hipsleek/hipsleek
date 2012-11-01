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

PROBLEM : Too many cases...
  Too complex result...

[ HP_585(v_node_48_627,x_628) ::= 
 H1(x_628)&x_628!=null
 or emp&x_628=null
 or G2(x_628,v_node_48_627)&true
 or H1(x_628)&true
 or HP_585(next_48_557',x_628)&true
 ,
 G2(x_625,v_node_45_626) ::= 
 G2(x_625,next_48_557')&true
 or H1(x_625)&true
 or HP_585(next_4GGG8_557',x_625)&true
 or H1(x_625)&x_625!=null
 or emp&x_625=null
  
 H1(x_624) ::= 
 x_624::node<val_49_559',next_49_560'> * 
 next_49_560'::node<val_48_556',next_48_622>&next_49_560'=null
 or x_624::node<val_49_559',next_49_560'> * 
    next_49_560'::node<val_48_556',next_48_622> * 
    G2(next_49_560',next_48_557')&true
 or x_624::node<val_49_559',next_49_560'> * 
    next_49_560'::node<val_48_556',next_48_622> * 
    HP_585(next_48_557',next_49_560')&true
 or emp&x_624=null
 or x_624::node<val_49_559',next_49_560'> * 
    next_49_560'::node<val_48_556',next_48_622> * H1(next_49_560')&true
 or x_624::node<val_49_559',next_49_560'> * 
    next_49_560'::node<val_48_556',next_48_622> * H1(next_49_560')&
    next_49_560'!=null
 

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




