data tree {
  node children;
}

data node {
  tree child;
  node sibling;
}

ptree<> ==
  self::tree<c>*c::sll<>;

sll<> ==
  self=null
or  self::node<c,n>*c::ptree<> * n::sll<>;

HeapPred H(tree a).
PostPred G(tree a).
HeapPred H2(node a).
PostPred G2(node a).

  void main(tree t)
  requires t::ptree<>
  ensures true;
{
  bool b = check_tree(t);
}


bool check_tree (tree t)
 requires t::ptree<>@L ensures res;
// infer [H,G,H2,G2] requires H(t) ensures G(t) & res;

{
   if (t==null) return false;
   //if (t.children==null) return true;
   else return check_child(t.children); 
}

bool check_child (node l)
  requires l::sll<>@L ensures  res;
//  infer [H,G,H2,G2] requires H2(l) ensures G2(l) & res;
{
	if (l==null) return true;
	return check_child(l.sibling)&& check_tree(l.child);
}

/*
# check-multi-tree.ss

We seems to be collecting only the relational assumption
of H2/G2 (from one of the method check_child). What happen to the
relational assumption of H/G (from check_tree)?
It seems not to have been collected.

[ H2(l)&l=null --> G2(l),
 H2(l)&l!=null --> l::node<child_38_955,sibling_38_956>@M * 
  HP_957(child_38_955) * HP_958(sibling_38_956),
 HP_958(sibling_38_956) --> H2(sibling_38_956),
 HP_957(child_38_955) --> H(child_38_955),
 l::node<child_38_955,sibling_38_956>@M * G2(sibling_38_956) * 
  G(child_38_955) --> G2(l)]

*/
