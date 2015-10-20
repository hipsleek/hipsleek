data node2{
	int val;
	node2 n;
	node2 s;
}

relation R(node2 x).
relation P(node2 x).
relation Q(node2 x).

bool skip1(node2 l)
  infer [@ana_ni,R,P,Q]
  requires R(l)
  ensures true;
{
  if (l==null) return true;
  else return skip1(l.s) && skip0(l.n,l.s);
}


bool skip0(node2 l, node2 e) 
  infer [@ana_ni,Q,P,R]
  requires P(l) & Q(e)
  ensures true;
{
  if (l == e) return true;
  else if (l==null) return false;
  else  return skip0(l.n, e) && l.s == null;
}


/*
************************************
******pure relation assumption 1 *******
*************************************
[RELASS [Q,P]: ( Q(e) & P(l)) -->  ((e<l & l<=0) | (l<=(e-1) & l<=0) | 2<=l | l=e),
RELDEFN Q: ( P(l) & 1<=l & l!=e' & Q(e')) -->  Q(e'),
RELDEFN P: ( 2<=v_node2_28_1699') -->  P(v_node2_28_1699'),
RELASS [Q,P]: ( Q(e) & P(l)) -->  ((e<l & l<=0) | (l<=(e-1) & l<=0) | 2<=l | l=e)]
*************************************

***************************************
** relation obligations after imm norm **
*****************************************
[RELASS [Q,P]: ( Q(e) & P(l)) -->  (2<=l | (l<=(e-1) & l<=0) | (e<l & l<=0) | l=e),
RELASS [Q,P]: ( Q(e) & P(l)) -->  (2<=l | (l<=(e-1) & l<=0) | (e<l & l<=0) | l=e)]
*****************************************



*************************************
******pure relation assumption 1 *******
*************************************
[RELASS [R]: ( R(l)) -->  l!=1,
RELDEFN R: ( 2<=v_node2_17_1723') -->  R(v_node2_17_1723')]
*************************************

***************************************
** relation obligations after imm norm **
*****************************************
[RELASS [R]: ( R(l)) -->  l!=1]
*****************************************

 */
