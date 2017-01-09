package simple.mirrorInterv;

public class MirrorInterv {

	/*

	 */
	public static void loop(int i) {
		int range = 20;
		while (-range <= i & i <= range) {
			if (range-i < 5 || range+i < 5) {
				i = i*(-1);
			} else {
				range++;
				i--;
				if (i == 0) {
					range = -1;
				}
			}
		}
		
	}
}
