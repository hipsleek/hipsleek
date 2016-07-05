data node {
  int val;
  node next;
}
HeapPred H(node a).
HeapPred G(node a, node b).
HeapPred G1(node a, node b).


HeapPred H1(node a).
HeapPred H2(node a).

void append(node@R x,node@R y)
  infer[H1,H2,G1]
  requires H1(x) * H2(y)
  ensures G1(x',y');//'
{
  if (x.next == null)
    x.next = y;
  else
    append(x.next, y);
}


/*
by hand:

H1(x)*H2(y)
for x.next :
	H1(x)*H2(y) -> x::node<_,b>
		state: HP_1(x,b)*H2(y)*x::node<_,b>
		constr: H1(x) -> HP_1(x,b)*x::node<_,b>
cond: x.next == null
	then-branch:
		HP_1(x,b)*H2(y)*x::node<_,b> & b = null
		HP_1(x,b)*H2(y)*x::node<_,b> & b = y
		end: HP_1(x,b)*H2(y)*x::node<_,b> & b = y -> G(x,y)
	else-branch:
		HP_1(x,b)*H2(y)*x::node<_,b> & b != null
		HP_1(x,b)*H2(y)*x::node<_,b> & b != null -> H1(b) * H2(y) --* G(b',y')
			state: G(b',y') * HP_1(x,b)*H2(y)*x::node<_,b> & b != null
			constr: HP_1(x,b)*H2(y)*x::node<_,b> & b != null -> H1(b) * H2(y)
		end: G(b',y') * HP_1(x,b)*H2(y)*x::node<_,b> & b != null -> G(x,y')

constrs:
H1(x) -> HP_1(x,b)*x::node<_,b>
HP_1(x,b)*H2(y)*x::node<_,y> & b = null-> G(x,y)
HP_1(x,b)*H2(y)*x::node<_,b> & b != null -> H1(b) * H2(y)
G(b',y') * HP_1(x,b)*H2(y)*x::node<_,b> & b != null -> G(x,y')

auto:

1. H1(x)  * H2(y) --->  x::node<val_22_526',next_22_527'> * HP_545(next_22_527',y,x)
2. HP_545(v_node_22_562,y,x) * x::node<val_22_551,y>&v_node_22_562=null ---> G1(x,y)
3. HP_545(v_node_22_568,y,x) * x::node<val_22_553,v_node_22_568>&v_node_22_568!=null --->  H1(v_node_22_568)* H2(y)
4. x::node<val_22_553,v_node_22_568> * G1(v_node_25_579,y') * HP_580(v_node_22_568,v_node_25_579,y',x,x)& v_node_22_568!=null ---> G1(x,y')
//4. HP_580(v_node_22_568,v_node_25_579,y',x,x) is generated.


*/


          /*
H1(x) --> x::node<val_25_530',next_25_531'> * HP_549(next_25_531',x)
HP_549(v_node_25_566,x) * x::node<val_25_555,y> & v_node_25_566=null --> G1(x,x,y)
HP_549(v_node_25_572,x) * x::node<val_25_557,v_node_25_572> & v_node_25_572!=null --> H1(v_node_25_572) * H2(y)
x::node<val_25_557,v_node_25_572> * G1(v_node_25_572,v_node_28_583,y) & v_node_25_572!=null --> G1(x,x,y)

H1(x) * H2(y) --> x::node<val_59_530',next_59_531'> * HP_549(next_59_531',y,x)
HP_549(v_node_59_566,y,x) * x::node<val_59_555,y> & v_node_59_566=null --> G1(x,x,y)
HP_549(v_node_59_572,y,x) * x::node<val_59_557,v_node_59_572>& v_node_59_572!=null --> H1(v_node_59_572) * H2(y)
x::node<val_59_557,v_node_59_572> * G1(v_node_59_572,v_node_62_583,y) & v_node_59_572!=null --> G1(x,x,y)

             */

/*
5-sep
by-hand:
H(x,y) -> H1(x,y,b) * x::node<_,b>
H1(x,y,b) * x::node<_,y> & b = null & x' = x & y' = y -> G(x,x',y,y')
H1(x,y,b) * x::node<_,b> & b != null & y' = y |- H(b,y')
G(b, b', y0, y') * x::node<_,b> & b != null & x' = x & y0 = y -> G(x,x',y,y')
auto:
H1(x) * H2(y)--> x::node<_,b> * HP_549(b,y,x)
HP_549(b,y,x) * x::node<_,y>&  b=null --> G1(x,x,y)
HP_549(b,y,x) * x::node<_,b>& b!=null--> H1(b) * H2(y)
x::node<_,b> *  G1(b,b',y)&b!=null --> G1(x,x,y)

//Matched
*/


/*
HP_545(v_node_18_562,y,x) * x::node<val_18_551,y>&v_node_18_562=null, G1(x,y)&true),
( H1(x) * H2(y)&true, x::node<val_18_526',next_18_527'> * HP_545(next_18_527',y,x)&true),
( HP_545(v_node_18_568,y,x) * x::node<val_18_553,v_node_18_568>&
v_node_18_568!=null, H1(v_node_18_568) * H2(y)&true),
( x::node<val_18_553,v_node_18_568> * G1(v_node_21_580,y') *
HP_581(v_node_18_568,v_node_21_580,y',x,x)&v_node_18_568!=null, G1(x,y')&true)]

 */
