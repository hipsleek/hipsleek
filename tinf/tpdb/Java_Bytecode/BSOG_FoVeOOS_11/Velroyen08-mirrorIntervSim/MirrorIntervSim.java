package simple.mirrorIntervSim;

public class MirrorIntervSim {

	/*

	 */
	public static void loop(int i) {
		while (i != 0) {
			if (-5 <= i && i <= 35) {
				if (i < 0) {
					i = -5;
				} else {
					if (i > 30) {
						i = 35;
					} else {
						i--;
					}	
				}					
			} else {
				i = 0;
			}
		}
	}
}
