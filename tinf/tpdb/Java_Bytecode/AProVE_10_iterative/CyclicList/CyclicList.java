/**
 * This class represents a list. The function get(n) can be used to access
 * the n-th element. 
 * @author Marc Brockschmidt
 */
public class CyclicList {
	/**
	 * A reference to the next list element.
	 */
	private CyclicList next;
	
	public static void main(String[] args) {
		CyclicList list = CyclicList.create(args.length);
		list.get(args[0].length());
	}
	
	/**
	 * Create a new list element.
	 * @param n a reference to the next element.
	 */
	public CyclicList(final CyclicList n) {
		this.next = n;
	}
	
	/**
	 * Create a new cyclical list of a length l.
	 * @param l some length
	 * @return cyclical list of length max(1, l)
	 */
	public static CyclicList create(int x) {
		CyclicList last, current;
		last = current = new CyclicList(null);
		while (--x > 0)
			current = new CyclicList(current);
		return last.next = current;
	}

	public CyclicList get(int n) {
		CyclicList cur = this;
		while (--n > 0) {
			cur = cur.next;
		}
		return cur;
	}	
}

