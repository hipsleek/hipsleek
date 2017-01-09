package simple.twoFloatInterv;

public class TwoFloatInterv {

	/*

	 */
	public static void loop(int i) {
		while (i > 0 & i < 50) {
			if (i < 20) {
				i--;
			}
			if (i > 10) {
				i++;
			}
			if (30 <= i && i <= 40) {
				i--;
			}
			
		}
	}
}
