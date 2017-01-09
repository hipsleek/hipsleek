package simple.complInterv3;

public class ComplInterv3 {

	public static void loop(int i) {
		while (i != 0) {
			if (i > 5) {
				i++;
			} else {
				if (i < -5) {
					i--;
				} else {
					i = 0;
				}
			}
		}
	}
}
