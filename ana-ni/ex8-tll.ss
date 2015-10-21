// tll with parent working example

data node{
	node parent;
	node left;
	node right;
	node next;
}
/*
tree<> == self::node<_,D1,null,_>
  or self::node<_,l,r,D2> * l::tree<> * r::tree<> & r!=null
	inv self!=null;

tll<p,ll,lr> == self::node<p,D1,null,lr> & self = ll
    or self::node<p,l,r,D2> * l::tll<self,ll,z> * r::tll<self,z,lr> & r!=null
	inv self!=null;

HeapPred H(node@NI p, node a, node@NI b).
HeapPred G(node a, node p, node b, node c).

*/

relation R(node x).
relation P(node x).
relation Q(node x).

  node set_right (node p, node x, node t) //expected @NI, @I, @NI
  infer [@ana_ni,R,P,Q]
  requires R(p) & P(x) & Q(t)
  ensures true;
{
  x.parent=p;
  if (x.right==null) {
    x.next = t;
    return x;
  }
  else {
    dprint;
    node l_most = set_right(x,x.right, t);
    return set_right(x,x.left, l_most);
  }
}

/*
******pure relation assumption 1 *******
*************************************
[RELASS [P]: ( P(x)) -->  2<=x,
RELDEFN P: ( 2<=v_node_38_1715') -->  P(v_node_38_1715'),
RELDEFN R: ( 2<=x' & P(x')) -->  R(x'),
RELDEFN Q: ( true) -->  Q(l_most')]
*************************************
 */
