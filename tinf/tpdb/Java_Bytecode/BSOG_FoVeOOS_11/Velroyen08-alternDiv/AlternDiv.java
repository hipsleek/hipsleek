package simple.alternDiv;

public class AlternDiv {

	public static void loop(int i) {
		while (i != 0) {
			if (i < 0) {
				i--;
				i = i*(-1);
			} else {
				i++;
				i = i*(-1);
			}
		}
	}
}
