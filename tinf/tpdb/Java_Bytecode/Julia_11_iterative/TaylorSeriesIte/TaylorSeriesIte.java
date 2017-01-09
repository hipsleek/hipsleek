public class TaylorSeriesIte {
    
    public static int power(int a, int b) {
	int p = 1;
	for (int i = 1; i <= b; i++) p *= a;
	return p;
    }

    public static int fact(int n) {
	int p = 1;
	for (int i = 1; i <= n; i++) p *= i;
	return p;
    }

    public static int sin(int x, int n) {
	int s = x;
	for (int i = 3; i <= n; i += 2)
	    s += power(-1, i/2) * power(x, i) / fact(i);
	return s;
    }

    public static int cos(int x, int n) {
	int s = 1;
	for (int i = 2; i <= n; i += 2)
	    s += power(-1, i/2) * power(x, i) / fact(i);
	return s;
    }

    public static int exp(int x, int n) {
	int s = 0;
	for (int i = 0; i <= n; i++)
	    s += power(x, i) / fact(i);
	return s;	
    }

    public static void main(String args[]) {
	for (int i = 0; i < args.length; i++)
	    if (i % 2 == 0) sin(args.length, i);
	    else if (i % 3 == 0) cos(args.length, i);
	    else if (i % 5 == 0) exp(args.length, i);
	    else for (int j = 0; j < 100; j++);
    }
}