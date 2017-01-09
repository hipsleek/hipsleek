package simple.complxStruc;

public class ComplxStruc {

	public static void loop(int i) {
		int j = i;
		while (i > 0) {
			if (i >= j) {
				i--;
				if (j < 5) {
					j++;
					if (i-j>2) {
						i++;
					} else {
						j++;
					}
				} else {
					j--;
				}
			} else {
				if (i > 0 & j < 0) {
					i--;
					if (j < -1) {
						j++;
					} else {
						i++;
					}
				} else {
					i++;
					if (j*2 > i) {
						j--;
					} else {
						j++;
					}
				}
			}
			
		}
	}
}
