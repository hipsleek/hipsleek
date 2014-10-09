public class NonPeriodic {

    public static void main(String args[]) {
	int x = 1, y = 0;

	if (args.length >= 1) {
	    y = -1*args[0].length();
	}

	// does not terminate for x = 1 and y = 1
	while (y > 0)
	    if (x > 0) x = x - 1;
	    else {
		y = y + 1;
		x = y;
	    }
    }
}