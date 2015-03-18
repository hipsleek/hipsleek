package simple.moduloUp;

public class ModuloUp {

	public static void up(int n) {
		int d = 10;
		while (n < 15) {
			n++;
			n = n % d;
		}
	}
}
