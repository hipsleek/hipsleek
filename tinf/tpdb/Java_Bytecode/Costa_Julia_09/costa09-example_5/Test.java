package example_5;

public class Test {
	/** 
	 * Execution of the main method does not terminate because in the call to
	 * m, the objects o1 and o2 are aliased and therefore by decrementing x.i we are 
	 * also decrementing this.i in the loop in method m.
	 */
	public static void main(String[] args) {
		Loops3 o1 = new Loops3();
		Loops3 o2 = o1;
		o1.m(10, o2);
	}

}
