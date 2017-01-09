public class DuplicateNodes {
    public static void main(String[] args) {
		Random.args = args;
        Tree tree = Tree.createTree();

		randomlyDuplicate(tree);
    }

	public static void randomlyDuplicate(Tree tree) {
		Tree cur = tree;
		
		while (cur != null) {
			if (Random.random() > 42) {
				cur.right = new Tree(cur.left, cur.right);
				cur = cur.left;
			} else {
				cur.left = new Tree(cur.left, cur.right);
				cur = cur.right;
			}
		}
	}
}
