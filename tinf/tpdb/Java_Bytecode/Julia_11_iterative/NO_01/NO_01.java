public class NO_01 {
    public static void main(String args[]) {
	int c = 24*60*60/100;
	if (c <= 10) 
	    for (int i = 0; i < 100; i++);
	else {
	    if (c <= 50) for (int i = 0; i < 101; i++);
	    if (c <= 100) for (int i = 0; i < 102; i++);
	    else for (int i = 0; i < 103; i += 0);
	}
    }
}