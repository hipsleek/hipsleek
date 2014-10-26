public class Choose {
    public static void main(String[] args) {
	int i = 3;
	while (i >= 3) {
	    if (i > 5)
		i += 3;
	    else if (i > 10)
		i -= 2;
	    else
		i++;
	}
    }
}