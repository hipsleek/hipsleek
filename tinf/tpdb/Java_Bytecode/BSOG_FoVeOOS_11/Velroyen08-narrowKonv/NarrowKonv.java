package simple.narrowKonv;

public class NarrowKonv {

	public static void loop(int i) {
		int range = 20;
		while (0 <= i && i <= range) {
			if (!(0 == i && i == range)) {
				if (i == range) {
					i = 0;
					range--;
				} else {
					i++;
				}
			}
		}
	}
}
