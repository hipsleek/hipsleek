public class NO_04 {
    public static void main(String args[]) {
        for (int i = 0; i < 100; i++) {
	    int a = i+2;
            for (int j = 0; j < a; j++)
		for (int k = i+j+3; k >= 0; k--) {
		    int b = i+j+k+4;
		    for (int l = 0; l < b; l++)
			for (int m = i+j+k+l+1000; m >= 0; m -= 0);
		}
	}
    }
}
