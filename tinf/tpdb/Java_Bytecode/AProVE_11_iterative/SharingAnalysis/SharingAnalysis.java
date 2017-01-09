package SharingAnalysis;

public class SharingAnalysis {
	int val;
	SharingAnalysis field;

	public static void main(String[] args) {
		Random.args = args;
		SharingAnalysis t1 = new SharingAnalysis();
		SharingAnalysis t2 = t1.appendNewList(1);
		SharingAnalysis t3 = t2.appendNewList(Random.random());
		t2.field = null;
		copy(t1, t3);
	}

	public static void copy(SharingAnalysis source, SharingAnalysis target) {
		while (source != null) {
			SharingAnalysis newEle = new SharingAnalysis();
			newEle.val = source.val;
			target.field = newEle;
			source = source.field;
			target = target.field;
		}
	}

	/**
 	 * @param i number of elements to append
 	 * @return the last list element appended
 	 */
	private SharingAnalysis appendNewList(int i) {
		this.field = new SharingAnalysis();
		SharingAnalysis cur = this.field;
		while (i > 1) {
			i--;
			cur = cur.field = new SharingAnalysis();
		}
		return cur;
	}
}
