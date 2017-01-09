package TreeLeftmostDepth;

public class TreeLeftmostDepth {
  public static void main(String[] args) {
    Random.args = args;
    Tree tree = Tree.createTree();
    int lmdepth = 0;
    while (tree.left != null) {
      /*      t              t
       *     / \            /  \
       *    tl  tr  ==>   tll   tl
       *   /  \                / \
       * tll  tlr            tlr  \tr
       */
      Tree tl = tree.left;
      Tree tll = tl.left;
      Tree tlr = tl.right;
      Tree tr = tree.right;
      tree.right = tl;
      tl.right = tr;
      tl.left = tlr;
      tree.left = tll;
      lmdepth++;
    }
  }
}
