public class LessLeaves {
  // Checks if a binary tree
  // has less leaves than another one

  public static void main(String[] args) {
    Random.args = args;
    Tree tree1 = Tree.createTree(); 
    Tree tree2 = Tree.createTree();
    boolean b = less_leaves(tree1,tree2);
  }



  public static Tree append(Tree t1, Tree t2) {

    Tree t;

    if (t1 == null) return t2;
    else {
      t = t1;

      while (t.right != null) {
        t = t.right;
      }

      t.right = t2;
      return t1;
    }
  }

  public static boolean less_leaves(Tree t1, Tree t2) {


    while ((t1 != null) && (t2 != null)) {
      t1 = append(t1.left,t1.right);
      t2 = append(t2.left,t2.right);
    }

    if (t2 == null) return false;
    else            return true;

  }
}
