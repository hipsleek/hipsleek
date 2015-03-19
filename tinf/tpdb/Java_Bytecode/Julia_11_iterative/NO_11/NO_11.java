public class NO_11 {
    public static void main(String args[]) {
	int j = 100;
	for (int i = 0; i < j; i++) {
	    if (i < j - 2) continue;
	    if (i > j - 2) break;
	    j++;
	}
   }
}