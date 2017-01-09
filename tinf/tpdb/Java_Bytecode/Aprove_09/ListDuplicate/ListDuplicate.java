/**
 * This class represents a list, where the function duplicate() can be used to
 * duplicate all elements in the list.
 * @author cotto
 */
public class ListDuplicate {
  /**
   * Walk through the list and, for each original element, copy it and append
   * this copy after the original. This transforms abc to aabbcc.
   */
  public static void duplicate(ObjectList list) {
    ObjectList current = list;
    boolean even = true;
    while (current != null) {
      // only copy the original elements!
      if (even) {
        final ObjectList copy =
          new ObjectList(current.value, current.next);
        current.next = copy;
      }
      current = current.next;
      even = !even;
    }
  }

  public static void main(String[] args) {
    Random.args = args;
    ObjectList list = ObjectList.createList();
    duplicate(list);
  }
}
