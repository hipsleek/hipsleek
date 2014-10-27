package simple.alternatingIncr;

public class AlternatingIncr {

	public static void increase(int i) {
		while (i > 0) {
			if (i % 2 == 0) {
				i--;
			} else {
				i = i+3;
			}
		}
	}
}
