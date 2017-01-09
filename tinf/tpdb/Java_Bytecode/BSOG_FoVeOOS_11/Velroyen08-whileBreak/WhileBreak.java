package simple.whileBreak;

public class WhileBreak {

	public static void loop(int i) {
		while (i > 10) {
			if (i > 20) {
				i++;
			} else {
				i--;
			}
			if (i == 30) {
				break;
			}
		}
	}
}
