public class Iterations {
    public static void main(String args[]) {
        for (int i = 0; i < args.length; i++) {
	    int a = 2*i;
            for (int j = 0; j < a; j++)
		for (int k = i+j; k >= 0; k--) {
		    int b = 2*i+3*j+4*k;
		    for (int l = 0; l < b; l++)
			for (int m = 1000*i+100*j+10*k+l; m >= 0; m--);
		}
	}
    }
}
