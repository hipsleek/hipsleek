package simple.plait;

public class Plait {
	
	// does not terminate for ???

	public static void loop(int i, int j, int k) {
		int plaitNext = 0;
		int swap = 0;
		while (i > 0 || j > 0 || k > 0) {
			if (plaitNext == 0) {
				swap = i;
				i = j/2;
				j = swap*2;
				plaitNext = 1;
			} else {
				swap = k;
				k = j*2;
				j = swap/2;
				plaitNext = 0;
			}
			
		}
	}
}
