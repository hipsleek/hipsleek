package simple.sunset;

public class Sunset {

	public static void loop(int i) {
		while (i > 10) {
			if (i == 25) {
				i = 30;
			}
			if (i <= 30) {
				i--;
			} else {
				i = 20;
			}
		}
	}
}
