package simple.gauss;

public class Gauss {

	// does not terminate for negative numbers 
	
	public static int sum(int n) {
		int sum = 0;
		while (n != 0) {
			sum += n;
			n--;
		}
		return sum;
	}

}
