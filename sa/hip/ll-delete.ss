data node {
	int val;
	node next;
}

ll<> == self=null
  or self::node<_,q>*q::ll<>
  inv true;

lseg<p> == self=p
  or self::node<_,q>*q::lseg<p>
  inv true;

l2<y> == self::node<a,null> & y=self
  or self::node<_,q>*q::l2<y> 
  inv y!=null;


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

new: 
 D(x)&x!=null, x::node<val_19_529',next_19_530'> * HP_557(next_19_530',x)&true),
( HP_557(v_node_19_531',x) * x::node<val_19_564,v_node_19_531'>&x!=null, D(v_node_19_531')&true),
( E(v_node_19_570,v_node_19_571) * x::node<Anon_577,Anon_578>&x'=null & 
x!=null, E(x,x') * HP_579(Anon_578,x)&true),
( D(x)&x=null, E(x,x)&true)



//RELATION3:
expect: x::node<_,b> * E(b,b') & x' = null -> E(x,x')
result: emp&x'=null & x!=null--> E(x,x')

NORMALLIZE:
	D(x) & x != null -> x::node<_,b> * D1(x,b)
	x::node<_,b> * D1(x,b) &x!=null-> D(b)
	x::node<_,b> * E(b,b') & x' = null -> E(x,x')
	D(x) & x == null -> E(x,x)
DROP
	D(x) & x != null -> x::node<_,b> * D1(b)
	x::node<_,b> * D1(b) &x!=null-> D(b)
	x::node<_,b> * E(b,b') & x' = null -> E(x,x')
	D(x) & x == null -> E(x,x)
SPLIT
E(x,x') <---> E1(x) * E2(x')
	D(x) & x != null -> x::node<_,b> * D1(b)
	x::node<_,b> * D1(b) &x!=null-> D(b)
	x::node<_,b> * E1(b) * E2(b') & x' = null -> E1(x) * E2(x')
	D(x) & x == null -> E1(x) * E2(x)
PICK PARTIAL DEFINED:
	x = null -> D(x)
	x = null -> E1(x)
	x = null -> E2(x)
	x::node<_,b> * E1(b) x!= null-> E1(x)
	E1 <-> ll
	D1(b)  & b != null -> b::node<_,b'> * D1(b')			//ll0+
	D1(b) -> D(b)
	D(x) & x != null -> x::node<_,b> * D(b)
	D(x) <--> ll
==> D,E1: ll, E2: x=null

auto:
D(x)&x!=null --> x::node<val_19_525',next_19_526'> * HP_549(next_19_526',x)
HP_549(v_node_19_527',x) * x::node<val_19_556,v_node_19_527'>&  x!=null --> D(v_node_19_527')
E(v_node_19_562,v_node_19_563) & x'=null & x!=null --> E(x,x')					//still lack info
D(x)&x=null --> E(x,x)
---defs----
HP_549(v_node_19_527')::  D(v_node_19_527')
D:  D(x)::   emp&x=null or x::node<val_19_525',next_19_526'> * D(next_19_526')
HP_565(x)::  emp&x=null,
HP_566(x)::  emp&x=null,
E(x,x)::  HP_565(x) * HP_566(x)

////////////////E(x,x') lack info




*/
