package simple.whileNestedOffset;

public class WhileNestedOffset {

	public static void increase(int i) {
		int j;
		while (i < 10) {
			j = i;
			while (j > 5) {
				j++;
			}
			i++;
		}
	}
}
