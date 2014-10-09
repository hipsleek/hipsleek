package simple.middle;

public class Middle {

	/*
	 * returns the number which is exactly between the first and the second
	 * input number, does not work if one number is even and one is odd or if i <
	 * j
	 */
	public static int middle(int i, int j) {
		while (i != j) {
			i--;
			j++;
		}
		return i;
	}
}
