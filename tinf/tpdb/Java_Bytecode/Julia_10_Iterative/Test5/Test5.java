public class Test5 {
    public static void main(String[] args) {
	List l1 = List.mk(args.length);
	List l2 = List.mk(args.length + 3);
	List l3 = List.mk(args.length + 5);
	List temp;

	while (length(l1) > 0) {
	    temp = l1;
	    l1 = l2;
	    l2 = l3;
	    l3 = temp;

	    if (length(l2) % 3 == 0)
		temp = temp.getTail();

	    if (length(l3) % 5 == 0)
		l3 = l3.getTail();

	    if (length(l1) > length(l2))
		l1 = l1.getTail();
	    else if (length(l1) == length(l2))
		l2 = l2.getTail();
	    else
		l3 = l3.getTail();

	    test(l1, l2, l3);
	}
    }

    private static int length(List list) {
	int len = 0;

	while (list != null) {
	    list = list.getTail();
	    len++;
	}

	return len;
    }

    private static void test(List l1, List l2, List l3) {
	while (l1 != null) {
	    l2 = new List(l1, l2);
	    l3 = new List(l2, l3);
	    l1 = l1.getTail();
	}
    }
}