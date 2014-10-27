public class Loop {
    public static void main(String[] args) {
	int a = 5;
	int b = 3;
	for (int i = 0; i < 10; i += 0) {}

	test(a, b);
    }

    private static int test(int a, int b) {
	return a * b;
    }
}