package example_5;

public class Loops3 extends Loops2 {
	
	/**
	 * A loop involving two numeric fields
	 * which are modified in the body of the loop
	 */
	public void m(int n, Loops3 x) {
		while (i < n) {
			i++;
			x.i--;
		}
		
	}
	
}
