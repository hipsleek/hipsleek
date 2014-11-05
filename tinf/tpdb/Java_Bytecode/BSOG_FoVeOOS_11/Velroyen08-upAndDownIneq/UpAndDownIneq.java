package simple.upAndDownIneq;

public class UpAndDownIneq {
	
	public static void upAndDown(int i) {
		int up = 0;
		while (0 <= i && i <= 10) {
			if (i >= 10) {
				up = 0;
			}
			if (i <= 0) {
				up = 1;
			}
			if (up >= 1) {
				i++;
			} else {
				i--;
			}
		}
	}
	
}
