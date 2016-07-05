public class Shuffle{

  // adapted from [Walther, 94]
  public static void main(String[] args) {
    Random.args = args;
    IntList l = IntList.createIntList();
    IntList res = null;

    while (l != null) {

      res = new IntList(l.value, res);
      l = l.next;
      if (l != null) l = l.reverse();

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
    int j;

    IntList l = null;

    while (i > 0) {
      j = Random.random();
      l = new IntList(j, l);
      i--;
    }

    return l;
  }

  public IntList reverse() {

    IntList res = null;
    IntList l = this;

    while (l != null) {
      res = new IntList(l.value, res);
      l = l.next;

    }

    return res;
  }
}
