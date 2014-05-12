data node {
  int val;
  node left;
  node right;
  node parent;
}

/*
 * predicate describes binary search tree data structure
 */
bstree <C> ==
     self = null & C = {}
     or self::node<v,l,r,_> * l::bstree<Cl> * r::bstree<Cr>
        & C = union({v}, Cl, Cr)
        & forall (x: (x notin Cl | x < v))
        & forall (x: (x notin Cr | x > v));

/*
 * Return max node and update new root in parameter "new_root"
 */
node extract_max(node root, ref node new_root)
  requires root::bstree<C> & root != null
  ensures new_root'::bstree<C1> * res::node<rv,_,rr,rp>
          & C1 = diff(C,{rv}) & rr = null & rp = null & rv in C
          & forall (x: (x notin C1) | x < rv);
{
  node max_node;
  node temp_root;
  if (root.right != null) {
    max_node = extract_max(root.right, temp_root);
    root.right = temp_root;
    if (temp_root != null)
      temp_root.parent = root;
    new_root = root;
    return max_node;
  }
  else {
    temp_root = root.left;
    root.parent = null;
    new_root = temp_root;
    return root;
  }
}
