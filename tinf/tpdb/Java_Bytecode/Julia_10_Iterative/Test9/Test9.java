public class Test9 {
    public static void main(String[] args) {
	long l = args.length;

	while (l > 0) {
	    for (int i = (int) l ; i < 100; i++)
		test(i);
	    l--;
	}
    }

    private static void test(int i) {
	int j, k, l, m;

	for (j = i; j > 0; j--);
	for (k = i; k > 0; k--);
	for (l = i; l > 0; l--);
	for (m = i; m > 0; m--);
	for (j = i; j > 0; j--);
	for (k = i; k > 0; k--);
	for (l = i; l > 0; l--);
	for (m = i; m > 0; m--);
	for (j = i; j > 0; j--);
	for (k = i; k > 0; k--);
	for (l = i; l > 0; l--);
	for (m = i; m > 0; m--);
    }
}