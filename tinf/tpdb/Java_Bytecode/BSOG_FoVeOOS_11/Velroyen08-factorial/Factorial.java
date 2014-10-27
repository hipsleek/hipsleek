package simple.factorial;

public class Factorial {
	public static int factorial(int j) {
		int i = 1;
		int fac = 1;
		while (fac != j) {
			fac = fac * i;
			i++;
		}
		return (i-1);
	}
}
