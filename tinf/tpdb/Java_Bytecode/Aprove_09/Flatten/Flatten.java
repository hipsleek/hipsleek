public class Flatten {
  public static void main(String[] args) {
    Random.args = args;
    int listLength = Random.random();
    TreeList list = null;
    for (int i = listLength; i > 0; i--) {
      Tree tree = Tree.createTree();
      list = new TreeList(tree, list);
    }

    flatten(list);
  }

  public static ObjectList flatten(TreeList start) {
    ObjectList result = null;
    while (start != null) {
      Tree tree = start.value;
      if (tree != null) {
        result = new ObjectList(tree.value, result);
        start = start.next;
        start = new TreeList(tree.left, start);
        start = new TreeList(tree.right, start);
      } else {
        start = start.next;
      }
    }
    return result;
  }
}
