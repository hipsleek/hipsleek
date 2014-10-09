package CyclicAnalysis;

public class CyclicAnalysis {
	CyclicAnalysis field;

	public static void main(String[] args) {
		Random.args = args;
		CyclicAnalysis t = new CyclicAnalysis();
		t.field = new CyclicAnalysis();
		t.field.appendNewCyclicList(Random.random());
		t.appendNewList(Random.random());
		t.length();
	}

	public int length() {
		int length = 1;
		CyclicAnalysis cur = this.field;
		while (cur != null) {
			cur = cur.field;
			length++;
		}
		return length;
	}

	public void appendNewCyclicList(int i) {
		CyclicAnalysis last = this.appendNewList(i);
		last.field = this;
	}

	/**
 	 * @param i number of elements to append
 	 * @return the last list element appended
 	 */
	private CyclicAnalysis appendNewList(int i) {
		this.field = new CyclicAnalysis();
		CyclicAnalysis cur = this.field;
		while (i > 1) {
			i--;
			cur = cur.field = new CyclicAnalysis();
		}
		return cur;
	}
}
