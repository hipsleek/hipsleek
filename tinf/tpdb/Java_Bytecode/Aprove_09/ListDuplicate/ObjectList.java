public class ObjectList {
  Object value;
  ObjectList next;

  public ObjectList(Object value, ObjectList next) {
    this.value = value;
    this.next = next;
  }

  public static ObjectList createList() {
    ObjectList result = null;
    int length = Random.random();
    while (length > 0) {
      result = new ObjectList(new Object(), result);
      length--;
    }
    return result;
  }
}
