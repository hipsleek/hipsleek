public class NO_05 {
    public static void main(String args[]) {
	for (int i = 0; i < 100; i++) {
	    if (i < 10) for (int j = 0; j < 15; j++);
	    else if (i < 50) continue;
	    else for (int j = 0; j < 15; j += 0);
	}
    }
}