package simple.ex06;

public class Ex06 {

	public static void loop(int i) {
		while (i >= -5 && i <= 5) {
			if (i > 0) {
				i--;
			}
			if (i < 0) {
				i++;
			}
		}
	}
}
