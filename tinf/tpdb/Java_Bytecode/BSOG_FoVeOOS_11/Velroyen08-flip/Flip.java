package simple.flip;

public class Flip {

	public static void flip(int i, int j) {
		int t = 0;
		while (i != 0 && j != 0) {
			t = i;
			i = j;
			j = t;
		}
	}
}
