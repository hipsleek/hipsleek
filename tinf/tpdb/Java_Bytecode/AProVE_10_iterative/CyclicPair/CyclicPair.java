public class CyclicPair {
	CyclicPair next;

	public static void main(String[] args) {
		Random.args = args;
		CyclicPair one = new CyclicPair();
		CyclicPair two = new CyclicPair();
		int i = Random.random();
		if (i == 0) { //two cyclic
			two.next = two;
		} else {      //one cyclic
			one.next = one;
		}

		while (two.next == two && one.next == one) {
			one.next = two;      //one: o1, two: o2 | o1: (next=o2), o2: (next=o2)
			two.next = one;      //one: o1, two: o2 | o1: (next=o2), o2: (next=o1)
			one.next = two.next; //one: o2, two: o2 | o1: (next=o1), o2: (next=o1)
			two.next = two;
		}
	}
}
