public class Test13 {
    private static List l1, l2;

    public static void main(String[] args) {
	List l = new List(13, null);
	List start = l;

	for (int i = 0; i < args.length + 1; i++) 
	    l = l.tail = new List(11, null);

	l1 = l;
	l2 = start;

	test();

	length(start);
    }

    private static int length(List l) {
	int length = 0;

	while (l != null) {
	    l = l.tail;
	    length++;
	}

	return length;
    }

    private static void test() {
	l1.tail = l2;
    }
}