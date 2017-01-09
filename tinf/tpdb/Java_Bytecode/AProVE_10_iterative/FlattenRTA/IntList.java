public class IntList {
  int value;
  IntList next;

  public IntList(int value, IntList next) {
    this.value = value;
    this.next = next;
  }

  public IntList() {
  }

  public static IntList createList() {
    IntList result = null;
    int length = Random.random();
    while (length > 0) {
      result = new IntList(Random.random(), result);
      length--;
    }
    return result;
  }
}
