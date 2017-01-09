package simple.complInterv2;

public class ComplInterv2 {

	public static void loop(int i) {
		while (i != 0) {
			if (i > -5 && i < 5) {
				if (i < 0) {
					i++;
				}
				if (i > 0) {
					i--;
				}
			} 			
		}
	}

}
