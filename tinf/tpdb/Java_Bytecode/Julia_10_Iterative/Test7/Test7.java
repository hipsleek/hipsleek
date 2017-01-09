public class Test7 {
    public static void main(String[] args) {
	List[] ls = { List.mk(args.length), List.mk(args.length), List.mk(args.length) };

	for (int k = 0; k < ls.length; k++) {
	    int len = length(ls[0]);
	    for (int i = 0; i < len; i++)
		bubble(ls[0]);
	}
    }

    private static void bubble(List l) {
	for (List cursor = l; cursor != null && cursor.getTail() != null; cursor = cursor.getTail())
	    if (cursor.head > cursor.getTail().head) {
		int temp = cursor.head;
		cursor.head = cursor.getTail().head;
		cursor.getTail().head = temp;
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