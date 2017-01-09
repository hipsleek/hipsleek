package simple.alternDivWide;

public class AlternDivWide {

	public static void loop(int i) {
		int w = 5;
		while (i != 0) {
			if (i < -w) {
				i--;
				i = i*(-1);
			} else {
				if (i > w) {
					i++;
					i = i*(-1);
				} else {
					i = 0;
				}
			}
		}
	}
}
