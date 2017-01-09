public class NullPair {
	NullPair next;

	public static void main(String[] args) {
		Random.args = args;
		NullPair one = null;
		NullPair two = null;
		int i = Random.random();
		if (i == 0) {
			one = new NullPair();
		} else {
			two = new NullPair();
		}

		while (one == null && two == null);
	}
}
