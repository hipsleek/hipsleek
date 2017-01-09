public class List1 {
	List1 pred, next;

	List1(List1 pred) {
		if (pred != null) {
			pred.next = this;
		}
		this.pred = pred;
	}

	static int length(List1 l) {
		int r = 1;
		while (null != (l = l.next))
			r++;
		return r;
	}

	public static void main(String[] args) {
		//Create doubly-linked list:
		int length = args.length;
		List1 cur = new List1(null);
		List1 first = cur;
		while (length-- > 0) {
			cur = new List1(cur);
		}

		length(first);		
	}
}

