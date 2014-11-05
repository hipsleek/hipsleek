package RetVal;

public class RetVal {
	public static void main(String[] args) {
		Random.args = args;
		int x = Random.random() % 2;
		int y = ret(x);
		test(x,y);
	}

	public static int ret(int x) {
		if (x == 0) return 1;
		else return 0;
	}

	public static boolean test(int x, int y) {
		while (x == y) {
			x--;
			y--;
		}
		return true;
	}
}
