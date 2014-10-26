public class DuplicateTreePath {
  public static void main(String[] args) {
    Random.args = args;
    Tree t = Tree.createTree();
    duplicateRandomPath(t);
  }

  public static void duplicateRandomPath(Tree tree) {
    Tree cur = tree;
    while (cur != null) {
      if (Random.random() < 42 && cur.left != null) { //go left
        Tree t = new Tree(cur.left, cur.right);
        t.value = cur.value;
        cur.right = null;
        cur.left = t;
        cur = cur.left.left;      
      } else if (cur.right != null) {                 //go right
        Tree t = new Tree(cur.left, cur.right);
        t.value = cur.value;
        cur.left = null;
        cur.right = t;
        cur = cur.right.right;
      } else {
        break;
      }
    }
  }
}
