public class Et2 {
    public static void main(String[] args) {
		Random.args = args;
	    int a =  Random.random(); 
	   	int b =  Random.random();	
	   	while (b > 0) {
	   		int r =  Random.random();		
	   		b = a - 1 - r;
	   	    a = a - 1 - r;
	   	}
    }
}

// bin(entry593(C,D),[1*C+ -1*B>=1,1*C+ -1*A>=1,1*D>=1],entry593(A,B))