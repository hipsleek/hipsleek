package simple.even;

public class Main {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
	    int even = args[1].length();
	    if (args[0].length() % 2 == 0) {
	        even = -even;
	    }
		Even.even(even);

	}

}
