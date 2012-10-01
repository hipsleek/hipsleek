data node {
	int val;
	node next;
}

void dispose(ref node x)
  requires x::node<_,_>
  ensures x'=null;//'

HeapPred D(node a).
HeapPred E(node a, node b).

void delete_list(ref node x)
  infer[D,E]
  requires D(x)
  ensures E(x,x');//'
{
  if (x!=null) {
    delete_list(x.next);
    //   dprint;
    x=null;
    //dispose(x);
  }
}

/*
D(x)&x!=null --> x::node<val_17_524',next_17_525'> * HP_548(next_17_525')
x!=null --> D(v_node_17_526')
D(x) & x!=null --> x::node<Anon_13,Anon_14> * HP_556(Anon_14)

E(x,y) = K(x)*L(y)

D(x) & x!=null --> x::node<val_19_525',next_19_526'> *  HP_549(next_19_526')
D(x) & x!=null --> x::node<Anon_13,Anon_14> * HP_561(Anon_14)
D(x) & x'=null & x!=null --> E(x,x')
D(x) & x=null --> E(x,x)
 */

/*
D(x) & x'=null & x!=null --> K(x) * L(x')
D(x) & x=null --> K(x) * L(x)

D(x) --> x = null --> emp
x=null --> K(x)
x=null <--> L(x)

D(x) & x!=null --> K(x)
D(x) & x=null --> K(x)
==> D(x) <---> K(x)

D(x) <---> x=null \/ x::node<val_19_525',next_19_526'> *  HP_549(next_19_526')


D(x) & x!=null --> x::node<val_19_525',next_19_526'> * HP_549(next_19_526',x)
HP_549(v_node_19_527',x) * x::node<val_19_556,v_node_19_527'> & x!=null --> D(v_node_19_527')
x'=null & x!=null --> E(x,x')
D(x) & x=null --> E(x,x)
 */


/*
by hand
D(x)
then: D(x) & x != null
e.next: D(x) & x != null |- x::node<_,b> * D1(x,b) &x!=null
rec: x::node<_,b> * D1(x,b) &x!=null-> D(b)
call: x::node<_,b> * E(b,b') & x' = null -> E(x,x')
else: D(x) & x == null -> E(x,x)

auto
D(x) & x!=null --> x::node<_,b> *  HP_549(b,x)
HP_549(b,x) * x::node<_,b>&x!=null --> D(b)
 emp&x'=null & x!=null--> E(x,x')
 D(x)&x=null --> E(x,x)

//RELATION3:
expect: x::node<_,b> * E(b,b') & x' = null -> E(x,x')
result: emp&x'=null & x!=null--> E(x,x')
*/
