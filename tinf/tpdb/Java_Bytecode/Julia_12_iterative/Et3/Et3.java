public class Et3 {
    public static void main(String[] args) {
		Random.args = args;
	    int a =  Random.random(); 
	   	int b =  Random.random();	
	   	while (a > 0) {
	   	    a = a + b;
	   	    b = b - 1;

	   	}
    }
}

// bin(entry(C,D),[C>=1,A=C+D,B=D-1],entry(A,B))