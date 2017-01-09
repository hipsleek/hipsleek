public class Et4 {
    public static void main(String[] args) {
		Random.args = args;
	    int a =  Random.random(); 
	   	int b =  Random.random();	
	    int c =  Random.random();	
	   	while ( (b - c >= 1) && (a == c)) {
	   		int r =  Random.random();
	   		b = 10;
	   		c = c + 1 + r;		
	   	    a = c;
	   	}
    }
}
