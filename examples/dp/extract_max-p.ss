data node {
  int val;
  node left;
  node right;
  node parent;
}

data pair {
  node new_root;
  node max_node;
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
pair extract_max(node root)
  requires root::bstree<C> & root != null
  ensures nr::bstree<C1> * res::pair<nr,nm> * nm::node<rv,_,null,null>
          & C = union(C1,{rv}) & forall (x: (x notin C1) | x < rv);
{
  node m; node c;
  if (root.right != null) {
    pair r = extract_max(root.right);
    c = r.new_root;
    m = r.max_node;
    root.right = c;
    if (c != null) c.parent = root;
    return new pair(root,m);
  }
  else {
    c = root.left;
    root.parent = null;
    return new pair(c,root);
  }
}


/*
procedure extract max(root: Node, implicit ghost content: set<int>)
4 returns (new root: Node, max: Node)
5 requires bstree(root, content) ✝ root ✘ null;
6 ensures bstree(new root, content ③ fmax.datag) ✝ acc(max);
7 ensures max.right ✏ null ❫ max.parent ✏ null ❫ max.data P content;
8 ensures (❅z P (content ③ fmax.datag)). z < max.data);
9 
10 var c: Node, m: Node;
11 if (root.right != null) { 
12 c, m := extract max(root.right, root);
13 root.right := c;
14 if (c != null) fc.parent := root;
15 return root, m;
16 } else {
17 c := root.left;
18 root.parent := null;
19 return c, root;
20 }
21 }
*/
