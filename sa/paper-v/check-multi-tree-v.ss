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
//infer [H,G,H2,G2] requires H2(l) ensures G2(l) & res;
{
	if (l==null) return true;
	return check_child(l.sibling)&& check_tree(l.child);
}

/*
# check-multi-tree.ss

If we had processed HP_987 before H, we would have been able
to inline away HP_987. This is because HP_987 is simpler
than H, and should be considered first.

[ H(t_1007) ::= t_1007::tree<children_30_986>@M * HP_987(children_30_986),
 H2(l_1009) ::= 
 H(child_38_997) * H2(sibling_38_996) * 
 l_1009::node<child_38_997,sibling_38_996>@M
 or emp&l_1009=null
 ,
 G2(l_1010) ::= 
 emp&l_1010=null
 or l_1010::node<child_38_955,sibling_38_956>@M * G2(sibling_38_956) * 
    G(child_38_955)
 ,
 G(t_1011) ::= t_1011::tree<children_30_986>@M * G2(children_30_986),
 HP_987(children_30_1008) ::= H2(children_30_1008)]

=======================================

 H2(l)&l!=null --> l::node<child_38_955,sibling_38_956>@M * 
  H_7(child_38_955) * H_8(sibling_38_956).

 H_8(sibling_38_956) --> H2(sibling_38_956).

 H_7(child_38_955) --> H(child_38_955).

 H2(l)&l=null --> G2(l),
 l::node<child_38_955,sibling_38_956>@M * G2(sibling_38_956) * 
  G(child_38_955) --> G2(l).


--------

 H(t)&t!=null --> t::tree<children_30_986>@M * H_9(children_30_986).

 H_9(children_30_986) --> H2(children_30_986).

 H(t) --> emp&t!=null.

 t::tree<children_30_986>@M * G2(children_30_986)&
  children_30_986=null --> G(t).

 t::tree<children_30_986>@M * G2(children_30_986)&
  children_30_986!=null --> G(t).



==========================

We seems to be collecting only the relational assumption
of H2/G2 (from one of the method check_child). What happen to the
relational assumption of H/G (from check_tree)?
It seems not to have been collected.

[ H2(l)&l=null --> G2(l),
 H2(l)&l!=null --> l::node<child_38_955,sibling_38_956>@M * 
  H_7(child_38_955) * H_8(sibling_38_956),
 H_8(sibling_38_956) --> H2(sibling_38_956),
 H_7(child_38_955) --> H(child_38_955),
 l::node<child_38_955,sibling_38_956>@M * G2(sibling_38_956) * 
  G(child_38_955) --> G2(l)]

!!! hp_lst_assume:[ H(t)&t!=null --> t::tree<children_30_986>@M * H_9(children_30_986),
 H_9(children_30_986) --> H2(children_30_986),
 H(t) --> emp&t!=null,
 t::tree<children_30_986>@M * G2(children_30_986)&
  children_30_986=null --> G(t),
 t::tree<children_30_986>@M * G2(children_30_986)&
  children_30_986!=null --> G(t)]


*/
