public class ListContentArbitrary{

  public static void main(String[] args) {
    Random.args = args;
    IntList l = IntList.createIntList();
    int n = Random.random();
    int m = l.nth(n);

    while (m > 0) m--;
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

  public int nth(int n){

    IntList l = this;

    while (n > 1) {
      n--;
      l = l.next;
    }

    return l.value;
  }
}

