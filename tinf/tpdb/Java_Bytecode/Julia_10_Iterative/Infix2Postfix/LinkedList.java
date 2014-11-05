public class LinkedList {
    private char head;
    private LinkedList tail;

    public LinkedList(char head, LinkedList tail) {
	this.head = head;
	this.tail = tail;
    }

    public char getFirst() {
	return this.head;
    }

    public LinkedList getTail() {
	return this.tail;
    }

    /*
    public String toString() {
	return head + (tail == null ? "" : " " + tail.toString());
    }
    */
}