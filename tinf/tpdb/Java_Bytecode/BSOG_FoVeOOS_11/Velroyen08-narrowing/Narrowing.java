package simple.narrowing;

public class Narrowing {

	public static void loop(int i) {
		int range = 20;
		boolean up = false;
		while (0 <= i && i <= range) {
			if (i == 0) {
				up = true;
			} 
			if (i == range) {
				up = false;
			}
			if (up) {
				i++;
			}
			if (!up) {
				i--;
			}
			if (i == range-2) {
				range--;
			}
		}
	}
}
