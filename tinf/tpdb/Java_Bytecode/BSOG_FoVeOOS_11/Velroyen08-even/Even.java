package simple.even;

public class Even {
	
	// does not terminate for negative numbers
	
	public static boolean even(int i) {
		while (i != 1 && i != 0) {
			i = i-2;
		}
		return (i == 0);
	}
}
