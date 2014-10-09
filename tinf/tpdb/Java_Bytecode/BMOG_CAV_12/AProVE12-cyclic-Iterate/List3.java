public class List3 {
	private List3 next;

	void iterate() {
		List3 current = this.next;
	        while (current != this) {
	                current = current.next;
	        }
	}

	public static void main(String[] args) {
		//Create cyclic list:
		int length = args.length;
		List3 cur = new List3();
		List3 first = cur;
		while (length-- > 0) {
			cur.next = new List3();
			cur = cur.next;
		}
		cur.next = first;

		cur.iterate();
	}
}
