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

     infer [H1,G2]
     requires H1(x)
     ensures G2(res,x);
/*
  requires x::ls2<> & x!=null
  ensures res::ls2<>;
  requires x::node<_,q>*q::ls2<> 
  ensures res::ls2<>;

Above forms are simpler ...


[ HP_695(v_node_68_693,x_694) ::= 
 emp&v_node_68_693=x_694 & v_node_68_623=null
 or emp&v_node_68_693=x_694
 or HP_695(v_node_68_623,v_node_68_606)&v_node_68_693=x_694 & 
    v_node_68_606!=null
 ,
 HP_668(next_66_556') ::= 
 next_66_556'::node<val_66_555',next_66_671> * HP_668(next_66_671)&true
 or v_node_68_657::node<val_66_555',next_66_673> * HP_668(next_66_673)&true
 or emp&v_node_68_643=null & next_66_556'=x_635
 o

*/
{
    bool b = rand();
	if (b) return x.next;
	else {
      if (x.next==null) return x;
      else {
         x.next = trav(x.next);
         return x;
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




