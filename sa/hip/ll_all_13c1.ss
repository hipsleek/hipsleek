
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

Precondition above rightly fail ...


Below is UNSOUND 

[ HP_666(v_node_56_664,x_665) ::= 
 HP_666(v_node_55_605,v_node_55_595)&v_node_56_664=x_665
 or emp&v_node_56_664=x_665
 ,
 HP_645(next_53_556') ::= 
 v_node_55_636::node<val_53_555',next_53_648> * HP_645(next_53_648)&true
 or emp&next_53_556'=x_617
 or next_53_556'::node<val_53_555',next_53_618>&next_53_618=x_619
 or next_55_622::node<val_53_555',next_53_621> * 
    next_53_556'::node<val_55_612,next_55_622>&true
 or next_55_625::node<val_55_610,next_55_625> * 
    next_53_556'::node<val_55_616,next_55_625>&true
 or emp


    bool b = rand();
	if (b) return x.next;
//H1(x) --> x::node<val_68_555',next_68_556'> * HP_577(next_68_556')
//HP_577(v_node_68_557') * x::node<val_68_601,v_node_68_557'>&true 
// --> G2(v_node_68_557',x)&true,
	else {
    x.next = trav(x.next);
//H1(x) --> x::node<val_70_558',next_70_559'> * HP_582(next_70_559')
//HP_582(v_node_70_560')&true --> H1(v_node_70_560')&true,
//G2(v_node_70_605,v_node_70_595) * 
//   x::node<val_70_588,v_node_70_605>&v_node_71_564'=x 
//   --> G2(v_node_71_564',x) * HP_607(v_node_70_605,x)
ERROR :  HP_607(v_node_70_605,x) should not be there..
      return x;

x::node<val_70_558',next_70_559'> * HP_582(next_70_559')
 |- H1(v_node_70_560') *-> G2(v_node_70_605,v_node_70_595)


 We got below:
 
 HP_643(next_129_556') ::= next_129_556'::node<val_129_555',next_129_652> 
      * HP_643(next_129_652)&true,
 G2(v_node_132_658,x_663) ::= G2(v_node_131_605,v_node_131_595) * 
        v_node_132_658::node<val_131_588,v_node_131_605>&true,
 H1(x_642) ::= x_642::node<val_129_555',next_129_556'> 
      * HP_643(next_129_556')&true]

      which is different from:
For 13c1, you should obtain:

  H1(x) = x:node<_,q>*H1(x)
  G2(res,_) <- H1(res)
  G2(res,_) <- G2(n,_)* res::node<_,n>

This indicates a problem since H1(x) did not have a base
case! Normalization should arise from:

//H1(x) --> x::node<val_68_555',next_68_556'> * HP_577(next_68_556')
//H1(x) --> x::node<val_70_558',next_70_559'> * HP_582(next_70_559')
==> HP_577 same as HP_582

//HP_582(v_node_70_560') --> H1(v_node_70_560'),
Hence:
  H1(x) = x:node<_,q>*H1(x)

For G2, we have:
//HP_577(v_node_68_557') * x::node<val_68_601,v_node_68_557'>&true 
// --> G2(v_node_68_557',x)&true,
//G2(v_node_70_605,v_node_70_595) * 
//   x::node<val_70_588,v_node_70_605>&v_node_71_564'=x 
//   --> G2(v_node_71_564',x)

which simplifies to:
//H1(res) * x::node<_,res> --> G2(res,x),
//G2(n,_)*x::node<_,n>&res=x --> G2(res,x) 

The presence of G2(n,_) indicates that there isn't a
formal link between res and x. Hence, we can rewrite to:

  G2(res,_) <- H1(res) * x::node<_,res>
  G2(res,_) <- G2(n,_)* res::node<_,n>

// dropping x:;node<_,res>, we obtain:

  G2(res,_) <- H1(res)
  G2(res,_) <- G2(n,_)* res::node<_,n>


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




