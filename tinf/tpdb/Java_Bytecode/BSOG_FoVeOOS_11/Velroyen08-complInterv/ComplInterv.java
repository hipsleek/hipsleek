package simple.complInterv;

public class ComplInterv {

	public static void loop(int i) {
		while (i*i > 9) {
			if (i < 0) {
				i = i-1;
			} else {
				i = i+1;
			}
		}
	}
	
}
