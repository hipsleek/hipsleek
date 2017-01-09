package TreeLeftmostPath;

public class TreeLeftmostPath {
  public static void main(String[] args) {
    Random.args = args;
    Tree tree = Tree.createTree();
    ObjectList result = null;
    while (tree.left != null) {
      /*      t              t
       *     / \            /  \
       *    tl  tr  ==>   tll   tl
       *   /  \                / \
       * tll  tlr            tlr  \tr
       */
      result = new ObjectList(tree.value, result);
      Tree tl = tree.left;
      Tree tll = tl.left;
      Tree tlr = tl.right;
      Tree tr = tree.right;
      tree.right = tl;
      tl.right = tr;
      tl.left = tlr;
      tree.left = tll;
    }
  }
}
