data tree {
  int val; 
  node children;
}

data node {
  tree child; 
  node next; 
  tree parent;
}


relation R(tree x).
relation P(node x).
relation Q(node x).

bool check_tree (tree t)
 infer [@ana_ni,R,P,Q]
  requires R(t)
  ensures true;
{
   if (t.children==null) return true;
   else return check_child(t.children,t);
}

bool check_child (node l, tree p)
  infer [@ana_ni,Q,P,R]
  requires P(l) & Q(p)
  ensures true;
{
  if (l==null) return true;
  else
    if (l.parent==p){
      dprint;
      return check_child(l.next, p) && check_tree(l.child);
    }
    else
      return false;
}

/*
*************************************
******pure relation assumption 1 *******
*************************************
[RELASS [R]: ( R(t)) -->  2<=t,
RELDEFN Q: ( 2<=t' & R(t')) -->  Q(t'),
RELDEFN P: ( 2<=v_node_23_1765') -->  P(v_node_23_1765'),
RELASS [P]: ( P(l)) -->  l!=1,
RELDEFN Q: ( 2<=p' & Q(p')) -->  Q(p'),
RELDEFN P: ( 2<=v_node_34_1738') -->  P(v_node_34_1738'),
RELDEFN R: ( 2<=v_tree_34_1744') -->  R(v_tree_34_1744')]
*************************************
***************************************
** relation obligations after imm norm **
*****************************************
[RELASS [R]: ( R(t)) -->  2<=t,
RELASS [P]: ( P(l)) -->  l!=1]
*****************************************


===>
RELDEFN Q: ( 2<=t' & R(t')) -->  Q(t'),
RELDEFN R: ( 2<=v_tree_34_1744') -->  R(v_tree_34_1744')
RELDEFN Q: ( 2<=p' & Q(p')) -->  Q(p'),

==>
2<=t' -->  Q(t') ??? not correct
 */
