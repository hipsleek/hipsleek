public class List {
    public int head;
    private List tail;

    public List(int head, List tail) {
	this.head = head;
	this.tail = tail;
    }

    public List getTail() {
	return tail;
    }

    public static List mk(int len) {
	List result = null;

	while (len-- > 0)
	    result = new List(len, result);

	return result;
    }
}