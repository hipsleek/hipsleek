/**
 * This class represents a list, where the function duplicate() can be used to
 * duplicate all elements in the list.
 * @author cotto
 */
public class CyclicalListDuplicate {
    /**
     * A reference to the next list element.
     */
    private CyclicalListDuplicate next;
    
    public static void main(String[] args) {
	CyclicalListDuplicate list = CyclicalListDuplicate.generate(args.length);
	if (list != null) {
	    list.duplicate();
	}
    }
    
    /**
     * Create a new list element.
     * @param n a reference to the next element.
     */
    public CyclicalListDuplicate(final CyclicalListDuplicate n) {
        this.next = n;
    }
    
    public static CyclicalListDuplicate generate(int length) {
	CyclicalListDuplicate last, current;
	last = current = new CyclicalListDuplicate(null);
	for (int i = 0; i < length - 1; i++) {
	    current = new CyclicalListDuplicate(current);
	}
	last.next = current;
	return current;
    }
    
    /**
     * Walk through the list and, for each original element, copy it and append
     * this copy after the original. This transforms abc to aabbcc.
     */
    public void duplicate() {
        CyclicalListDuplicate current = this;
        boolean even = true;
        while (current != null) {
            // only copy the original elements!
            if (even) {
                final CyclicalListDuplicate copy = new CyclicalListDuplicate(current.next);
                current.next = copy;
            }
            current = current.next;
            even = !even;
        }
    }
}
