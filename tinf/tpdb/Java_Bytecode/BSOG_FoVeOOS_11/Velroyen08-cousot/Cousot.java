package simple.cousot;

public class Cousot {

	public static void loop(int i, int j) {
		while (true) {
			if (i < j) {
				i = i+4;
			} else {
				j = j+1;
				i = i+2;
			}
		}
	}
}
