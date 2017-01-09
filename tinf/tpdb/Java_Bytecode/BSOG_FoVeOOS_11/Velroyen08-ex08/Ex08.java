package simple.ex08;

public class Ex08 {

	public static void loop(int i) {
		boolean up = false;
		while (i > 0) {
			if (i == 1) {
				up = true;
			}
			if (i == 10) {
				up = false;
			}
			if (up) {
				i++;
			} else {
				i--;
			}
		}
	}
}
