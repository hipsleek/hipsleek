package simple.alternKonv;

public class AlternKonv {
 
	public static void loop(int i) {
		while (i != 0) {
			if (i < 0) {
				i = i+2;
				if (i < 0) {
					i = i*(-1);
				}
			} else {
				i = i-2;
				if (i > 0) {
					i = i*(-1);
				}
			}
		}
	}
}
