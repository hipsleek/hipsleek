package javaUtilEx;

public class juLinkedListCreateIteratorLoop {
	public static void main(String[] args) {
		Random.args = args;

		LinkedList<Content> l = createList(Random.random());
		Iterator<Content> it = l.iterator();
		while (it.hasNext()) {
			it.next();
		}
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
