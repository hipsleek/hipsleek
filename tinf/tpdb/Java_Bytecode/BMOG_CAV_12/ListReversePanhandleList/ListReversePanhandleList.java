public class ListReversePanhandleList {
	public static void main(String... args) {
		List x = List.createPanhandleList(args[0].length(), args[1].length());
		List.reverse(x);
	}
}

class List {
	List n;

	public List(List next) {
		this.n = next;
	}

	public static void reverse(List x) {		
		List y = null;
		while (x != null) {
			List z = x;
			x = x.n;
			z.n = y;
			y = z;
		}
	}

	public static List createList(int l, List end) {
		while (--l > 0) {
			end = new List(end);
		}
		return end;
	}

	public static List createCycle(int l) {
		List last = new List(null);
		List first = createList(l - 1, last);
		last.n = first;
		return first;
	}

	public static List createPanhandleList(int pl, int cl) {
		return createList(pl, createCycle(cl));
	}

}
