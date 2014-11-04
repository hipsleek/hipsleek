package javaUtilEx;

public class juLinkedListCreateSubList {
	public static void main(String[] args) {
		Random.args = args;

		LinkedList<Content> l1 = createList(Random.random());
		List<Content> l2 = l1.subList(Random.random(), Random.random());
	}

	public static LinkedList<Content> createList(int n) {
		LinkedList<Content> l = new LinkedList<Content>();
		while (n > 0) {
			l.addLast(new Content(Random.random()));
			n--;
		}
		return l;
	}
}

final class Content {
	int val;

	public Content(int v) {
		this.val = v;
	}

	public int hashCode() {
		return val^31;
	}

	public boolean equals(Object o) {
		if (o instanceof Content) {
			return this.val == ((Content) o).val;
		}
		return false;
	}
}
