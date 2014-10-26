package simple.ex01;

public class Main {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
        int value = args[1].length();
        if (args[0].length() % 2 == 0) {
            value = -value;
        }
		Ex01.loop(value);
	}

}
