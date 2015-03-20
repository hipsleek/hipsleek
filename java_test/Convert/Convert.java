public class Convert{

  // adapted from [Giesl, 95]
  // converts a number to decimal notation

  public static void main(String[] args) {
    Random.args = args;
    IntList l = IntList.createIntList();

    int b = Random.random();
    int res = 0;

    while (l != null) {

      if (l.value <= 0) {
        l = l.next;
        if (l != null) res = res * b;
      }
      else {
        l.value--;
        res++;
      }
    }
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
