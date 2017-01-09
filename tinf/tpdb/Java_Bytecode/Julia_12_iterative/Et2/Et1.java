public class Et1 {
    public static void main(String[] args) {
		Random.args = args;
	    int a = - Random.random(); 
	   	int b = - Random.random();	
	   	while (a > b) {
	   		b = b + a;
 			a = a + 1;
	   	}
    }
}
