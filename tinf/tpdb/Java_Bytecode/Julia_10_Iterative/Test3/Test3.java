public class Test3 {
    public static void main(String[] args) {
	List l1 = List.mk(args.length);
	List l2 = List.mk(args.length);
	List l3 = (args.length % 2 == 0) ?
	    List.mk(args.length * args.length) : l2;

	while (length(l1) + length(l2) + length(l3) * 5 > 0)
	    if (length(l1) % 2 == 1)
		l1 = l1.getTail();
	    else if (length(l2) > length(l3))
		l2 = l2.getTail();
	    else if (l3 == null)
		break;
	    else {
		l1 = new List(new Object(), l1);
		l2 = new List(new Object(), l2);
		l3 = l3.getTail();
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
}
