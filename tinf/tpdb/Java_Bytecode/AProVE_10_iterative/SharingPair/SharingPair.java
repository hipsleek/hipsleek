public class SharingPair {
	SharingPair next;

	public static void main(String[] args) {
		Random.args = args;
		SharingPair one = new SharingPair();
		SharingPair two = new SharingPair();
		SharingPair cur;
		int i = Random.random();
		if (i == 0) {
			one.next = two;
			cur = one;
		} else {
			two.next = one;
			cur = two;
		}

		while (true) {
			if (i == 0) {
				one.next = new SharingPair();
				cur = cur.next;
			} else {
				two.next = new SharingPair();
				cur = cur.next;
			}
		}
	}
}
