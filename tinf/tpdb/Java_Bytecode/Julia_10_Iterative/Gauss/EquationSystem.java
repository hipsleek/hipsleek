public class EquationSystem {
    private Rational A[][];
    private Rational b[];
    private int n;

    public EquationSystem(Rational A[][], Rational b[]) {
	this.n = A.length;
	this.A = new Rational[n][n];
	this.b = new Rational[n];	
	for (int l = 0; l < n; l++) {
	    for (int c = 0; c < n; c++)
		this.A[l][c] = A[l][c]; 
	    this.b[l] = b[l];
	}
    }

    /*
    public void resolve() {
	if (diagonalize()) {
	    System.out.print("One solution = ");
	    System.out.print("(");
	    for (int l = 0; l < n; l++) {
		System.out.print(b[l]);
		if (l < n-1) System.out.print("; ");
	    }
	    System.out.println(").");
	}
	else System.out.println("Zero or an infinite number of solutions.");
    }
    */

    private int searchRow(int col) {
	for (int l = col; l < n; l++)
	    if (!A[l][col].isZero()) return l;
	return n;
    }

    private void permute(int l1, int l2) {
	Rational temp;
	for (int col = l1; col < n; col++) {
	    temp = A[l1][col];
	    A[l1][col] = A[l2][col]; 
	    A[l2][col] = temp;
	}
	temp = b[l1];
	b[l1] = b[l2];
	b[l2] = temp;
    }

    private void divide(int l, Rational pivot) {
	for (int col = l; col < n; col++) A[l][col].divideBy(pivot);
	b[l].divideBy(pivot);
    }

    private void substract(int i, int j) {
	Rational A_ji = new Rational(A[j][i]);
	for (int col = i; col < n; col++)
	    A[j][col].minus(A_ji.times(A[i][col]));
	b[j].minus(A_ji.times(b[i]));
    }

    public boolean diagonalize() {
	int current;
	Rational p;
	
	for (int l = 0; l < n; l++) {
	    current = searchRow(l);
	    if (current == n) return false;
	    p = new Rational(A[current][l]);
	    permute(l, current);
	    divide(l, p);
	    for (int ll = 0; ll < n; ll++)
		if (ll != l) substract(l, ll);
	}
	
	return true;
    }

    /*
    public String toString() {
	String res = "";
	for (int l = 0; l < n; l++) {
	    for (int col = 0; col < n-1; col++)
		res += A[l][col] + "*X" + col + " + ";
	    res += A[l][n-1] + "*X" + (n-1) + " = " + b[l] + "\n";
	}
	return res;
    }
    */

    public static void main (String args[]) {
	if (args.length >= 4) {
	    Rational A[][] = new Rational[1][1];
	    Rational b[]   = new Rational[1];
	    
	    A[0][0] = new Rational(args[0].length(), args[1].length());
	    b[0] = new Rational(args[2].length(), args[3].length());
	    
	    EquationSystem S = new EquationSystem(A, b);
	    // System.out.println(S);
	    // S.resolve();
	    S.diagonalize();
	}
    }
}
