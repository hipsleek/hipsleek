package simple.lcm;

public class Lcm {

	// does not terminate if exactly one of the input values is negative
	
	public static int lcm (int a, int b) {
		int am = a;
		int bm = b;
		
		while (am != bm) {
			if (am > bm) {
				bm = bm+b;
			} else {
				am = am+a;
			}
		}
		return am;
	}
}
