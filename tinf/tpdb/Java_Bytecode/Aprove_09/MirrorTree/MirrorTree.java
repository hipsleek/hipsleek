public class MirrorTree {
    public static void main(String[] args) {
		Random.args = args;
        Tree tree = Tree.createTree();

        //Now mirror the left-most path:
		mirror(tree);
    }

	public static void mirror(Tree tree) {
		Tree cur = tree;
        while (cur != null) {
            Tree t = cur.left;
            cur.left = cur.right;
            cur.right = t;
            cur = cur.right;
        }	
	}
}
