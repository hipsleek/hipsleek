public class Et5 {
    public static void main(String[] args) {
		Random.args = args;
	    int a =  Random.random(); 
	   	int b =  Random.random();	
	    int c =  Random.random();	
	   	while (c >= 0) {
	   		int ap = Random.random();
	   		int bp = Random.random();
	   		if ( 2*a -b <= 2*ap-bp ) break;
	   		a = ap;
	   		b = bp;
	   		c = c + 2*a -b;
	   	}
    }
}

/*
entry(A,B,X) :-
{2*A-B >= 1+2*C-D, X>=0,Y=X+2*C-D},
entry(C,D,Y).
*/
