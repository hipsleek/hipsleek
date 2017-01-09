public class List2 {
	private List2 next;
	private int mark;

	static void visit(List2 c) {
		int expectedMark = c.mark;
		while (c != null && c.mark == expectedMark) {
			c.mark = expectedMark + 1;
			c = c.next;
		}
	}

	public static void main(String[] args) {
		//Create cyclic list:
		int length = args.length;
		List2 cur = new List2();
		List2 last = cur;
		while (length-- > 0) {
			List2 n = new List2();
			n.next = cur;
			cur = n;
		}
		last.next = cur;

		visit(cur);		
	}
}

