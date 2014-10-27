public class FlattenRTA {
  public static IntList flatten(TreeList list) {
    TreeList cur = list;
    IntList result = null;
    while (cur != null) {
      Tree tree = cur.value;
      if (tree != null) {
        IntList oldIntList = result;
        result = new IntList();
        result.value = tree.value;
        result.next = oldIntList;
        TreeList oldCur = cur;
        cur = new TreeList();
        cur.value = tree.left;
        cur.next = oldCur;
        oldCur.value = tree.right;
      } else cur = cur.next;
    }
    if (cur != list) {}
    return result;
  }

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
}
