public class Rational {
    private int n, d;

    public Rational() {
	n = 0; d = 1;
    }

    public Rational(int num, int den) { 
	n = num; d = den;
    }

    public Rational(Rational r) {
	n = r.n; d = r.d;
    }

    public void minus(Rational r) {
	n = n*r.d - r.n*d;
	d *= r.d;
	simplify();
    }

    public Rational times(Rational r) {
	Rational result = new Rational(n*r.n, d*r.d);
	result.simplify();
	return result;
    }

    public void divideBy(Rational r) {
	n *= r.d; 
	d *= r.n;
	simplify();
    }

    private static void eratosthene(boolean T[]) {  
	for (int i = 0; i < T.length; i++) T[i] = false;
	if (T.length  <= 4) return;
	int number = 1;
	while (number*number < T.length) {
	    while ( T[++number] && number < T.length ) {};
	    for (int i = 2*number; i < T.length; i += number)
		T[i] = true;
	}
    }

    private static int min(int a, int b) {
	if (a < b) return a;
	else return b;
    }

    private static int abs(int a) {
	if (a < 0) return -1*a;
	else return a;
    }

    public void simplify() {
	int nn = abs(n), dd = abs(d);
	int limite = min(nn, dd);

	boolean divisible[] = new boolean[limite + 1];
	eratosthene(divisible);

	boolean go_on = true;
	while (go_on) {
	    go_on = false;
	    for (int i = 2; i <= limite; i++)
		if (!divisible[i])
		    if (nn%i == 0 && dd%i == 0) {
			nn /= i; dd /= i;
			limite = min(nn, dd);
			go_on = true;
			break;
		    }
	}
	
	if ( (n >= 0 && d >= 0) || (n <= 0 && d <= 0) ) { n = nn; d = dd; }
	else { n = -1*nn; d = dd; }
    }


    public boolean isZero() {
	return n == 0;
    }

    /*
    public String toString() {
	String result = new String();
	result += n;
	if (n != 0 && d != 1) result += "/" + d; 
	return result;
    }
    */
}