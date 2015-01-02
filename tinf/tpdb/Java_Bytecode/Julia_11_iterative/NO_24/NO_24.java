public class NO_24 {
    public static void main(String args[]) {
	int a = 1, b = 2;

	while (a + b < 5) {
	    a = a - b;
	    b = a + b;
	    a = b - a;
	}
    }
}
