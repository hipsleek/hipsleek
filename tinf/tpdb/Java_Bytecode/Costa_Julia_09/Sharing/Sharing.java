public class Sharing {

    private Sharing next;

    public Sharing(Sharing next) {
	this.next = next;
    }

    public void iter(Sharing other) {
	Sharing cursor = this;

	while (cursor != null) {
	    other.next = new Sharing(null);
	    other = other.next;

	    cursor = cursor.next;
	}
    }

    public static void main(String[] args) {
	Sharing sh1 = new Sharing(new Sharing(new Sharing(null)));
	Sharing sh2 = new Sharing(new Sharing(null));
	sh2.next.next = sh2;
	sh1.iter(sh2);
    }
}