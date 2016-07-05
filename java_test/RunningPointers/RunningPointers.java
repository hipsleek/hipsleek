/**
 * Allegedly based on an interview question at Microsoft.
 */
public class RunningPointers {

  public static boolean isCyclic(ObjectList l) {
    if (l == null) {
      return false;
    }
    ObjectList l1, l2;
    l1 = l;
    l2 = l.next;
    while (l2 != null && l1 != l2) {
      l2 = l2.next;
      if (l2 == null) {
        return false;
      }
      else if (l2 == l1) {
        return true;
      }
      else {
        l2 = l2.next;
      }
      l1 = l1.next;
    }
    return l2 != null;
  }

  public static void main(String[] args) {
    Random.args = args;
    ObjectList list = ObjectList.createList();
    isCyclic(list);
  }
}
