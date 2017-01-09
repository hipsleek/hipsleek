public class CountMetaList {
	public static void main(String[] args) {
		Random.args = args;
		List l = createMetaList();

		int count = countMetaList(l);
	}

	public static int countMetaList(List cur) {
		int res = 0;
		while (cur != null) {
			if (cur.value instanceof List) {
				List inner = (List) cur.value;
				cur.value = inner.next;
				cur = new List(inner.value, cur);
			}
			cur = cur.next;
			res++;
		}

		return res;
	}

	public static List createMetaList() {
		int count = Random.random();
		List cur = null;
		for (int i = 0; i < count; i++) {
			int innerCount = Random.random();
			List innerList = null;
			for (int j = innerCount; j > 0; j--) {
				innerList = new List(null, innerList);
			}
			cur = new List(innerList, cur);
		}

		return cur;
	}
}

class List {
	Object value;
	List next;

	public List(Object v, List n) {
		this.value = v;
		this.next = n;
	}
}
