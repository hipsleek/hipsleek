package simple.whileNested;

public class WhileNested {

	public static void increase(int i) {
		int j;
		while (i < 10) {
			j = i;
			while (j > 0) {
				j++;
			}
			i++;
		}
	}
}
