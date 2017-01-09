package example_2;


public class Test {

	public static int divBy(int x){
		int r = 0;
		int y;
		while (x > 0) {
			y = 2;
			x = x/y;
			r = r + x;
		}
		return r;
	}

	public static void main(String[] args) {
		if (args.length > 0) {
		        int x = args[0].length();
			int r = divBy(x);
			// System.out.println("Result: " + r);
		}
		// else System.out.println("Error: Incorrect call");
	}
}
