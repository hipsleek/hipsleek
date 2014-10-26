public class Samefringe {
  // from [Boyer&Moore,1979]. Checks if 2 binary trees
  // have the same number of nodes
  public static void main(String[] args) {
    Random.args = args;
    Tree tree1 = Tree.createTree(); 
    Tree tree2 = Tree.createTree();
    samefringe(tree1,tree2);
  }

  public static Tree gopher(Tree start) {

    Tree s,t,u;

    while ((start != null) && (start.left != null)){
      s = start.left.left;
      t = start.left.right;
      u = start.right;
      start = new Tree(s, new Tree(t,u));
    }
    return start;
  }


  public static boolean samefringe(Tree t1, Tree t2) {
    while ((t1 != null) && (t2 != null)) {
      t1 = gopher(t1).right;    
      t2 = gopher(t2).right;
    }
    return ((t1 == null) && (t2 == null));
  }
}
