public class ListContent{

  public static void main(String[] args) {
    Random.args = args;
    IntList l = IntList.createIntList();

    while (l.value > 0) l.value--;
  }

}

class IntList {
  int value;
  IntList next;

  public IntList(int value, IntList next) {
    this.value = value;
    this.next = next;
  }

  public static IntList createIntList() {

    int i = Random.random();
    IntList l = null;

    while (i > 0) {
      l = new IntList(Random.random(), l);
      i--;
    }

    return l;
  }
}
