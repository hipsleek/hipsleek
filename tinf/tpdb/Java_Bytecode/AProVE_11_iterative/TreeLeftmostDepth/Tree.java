package TreeLeftmostDepth;

public class Tree {
  Tree left;
  Tree right;
  Object value;

  public Tree(Tree l, Tree r) {
    this.left = l;
    this.right = r;
  }

  public Tree() {
  }

  public static Tree createNode() {
    Tree result = new Tree();
    result.value = new Object();
    return result;
  }

  public static Tree createTree() {
    int counter = Random.random();
    if (counter == 0) {
      return null;
    }
    Tree result = createNode();
    Tree t = result;

    while (counter > 0) {
      int branch = Random.random();
      if (branch > 0) {
        if (t.left == null) {
          t.left = createNode();
          t = result;
        } else {
          t = t.left;
        }
      } else {
        if (t.right == null) {
          t.right = createNode();
          t = result;
        } else {
          t = t.right;
        }
      }
      counter--;
    }

    return result;
  }
  public static void main(String[] args) {
    Random.args = args;
    createTree();
  }
}
