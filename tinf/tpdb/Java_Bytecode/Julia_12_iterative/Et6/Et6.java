public class Et6 {
    public static void main(String[] args) {
		Random.args = args;
	    int a =  Random.random(); 
	   	int b =  Random.random();	
	    int c =  Random.random();	
	   	while (c >= 0) {
	   		int ap = Random.random();
	   		int bp = Random.random();
	   		if ( 3*b - 2*a >= 3*bp - 2*ap) break;
	   		a = ap;
	   		b = bp;
	   		c = c - (3*b-2*a);
	   	}
    }
}

