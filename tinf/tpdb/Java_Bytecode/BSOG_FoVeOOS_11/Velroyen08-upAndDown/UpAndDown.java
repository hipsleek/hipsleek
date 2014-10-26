package simple.upAndDown;

public class UpAndDown {

	public static void upAndDown(int i) {
		boolean up = false;
		while (0 <= i && i <= 10) {
			if (i == 10) {
				up = false;
			}
			if (i == 0) {
				up = true;
			}
			if (up) {
				i++;
			} else {
				i--;
			}
		}
	}
}
