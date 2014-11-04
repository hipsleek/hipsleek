public class List {
    public Object head;
    private List tail;

    public List(Object head, List tail) {
	this.head = head;
	this.tail = tail;
    }

    public List getTail() {
	return tail;
    }

    public static List mk(int len) {
	List result = null;

	while (len-- > 0)
	    result = new List(new Object(), result);

	return result;
    }
}