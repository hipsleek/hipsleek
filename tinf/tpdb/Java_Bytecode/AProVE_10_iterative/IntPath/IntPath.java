public class IntPath {
    public static void main(String[] args) {
        Random.args = args;
        int i = Random.random();
		int x = 0;
		int y = 0;
		if (i > 10) {
			x = 1;
		} else {
			y = 1;
		}
		while (x == y);
    }
}
