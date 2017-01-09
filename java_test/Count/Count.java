public class Count {
  public static void main(String[] args) {
    Random.args = args;
    Tree tree = Tree.createTree();

    int c = count(tree);
  }

  public static Tree flatten(Tree start) {
    Tree result = null;
    Tree s,t,u;

    while (start != null) {

      if (start.left == null) {

        result = new Tree(null,result);
        start = start.right;
      }
      else {
        s = start.left.left;
        t = start.left.right;
        u = start.right;
        start = new Tree(s, new Tree(t,u));



      }
    }

    return result;
  }


  public static int count(Tree start) {

    int res = 0;

    while (start != null) {

      if (start.left == null) {

        res++;
        start = start.right;
      }
      else {
        start = flatten(start);    

      }
    }

    return res;
  }
}
