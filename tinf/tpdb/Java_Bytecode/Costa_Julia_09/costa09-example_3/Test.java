package example_3;

public class Test {
	int i;
	
	/**
	 * Same simple arithmetic loop, but the loop counter
	 * is a numeric field.
	 */
	public void m(int n) {
		while (i < n) {
			i++;
		}
	}
	
	public static void main(String[] args) {
		Test o = new Test();
		o.m(10);
	}

}
