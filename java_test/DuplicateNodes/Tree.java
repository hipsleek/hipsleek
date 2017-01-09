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
   if (Random.random() == 0) {
      return null;
    }
    Tree result = new Tree();
    return result;
  }

  public static Tree createTree() {
    Tree result = createNode();
    List list = new List(result, null);
    
    int counter = Random.random();
    while (counter > 0 && list != null) {
      Tree first = list.value;
      list = list.next;

      if (first != null) {
        Tree left = createNode();
        Tree right = createNode();
        first.left = left;
        first.right = right;
        list = new List(left, list);
        list = new List(right, list);
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
