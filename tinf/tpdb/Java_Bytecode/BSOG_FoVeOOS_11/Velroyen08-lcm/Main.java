package simple.lcm;


public class Main {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
        int x = args[2].length();
        int y = args[3].length();
        if (args[0].length() % 2 == 0) {
            x = -x;
        }
        if (args[1].length() % 2 == 0) {
            y = -y;
        }
		Lcm.lcm(x, y);
	}

}
