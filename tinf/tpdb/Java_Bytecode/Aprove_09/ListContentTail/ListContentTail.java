public class ListContentTail{

  public static void main(String[] args) {
    Random.args = args;
    IntList l = IntList.createIntList();

    int m = IntList.nth(Random.random(),l);

    while (m > 0) {

      l = l.next;
      m = IntList.nth(Random.random(),l);
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

  public static int nth(int n, IntList l){

    while (n > 1 && l != null) {
      n--;
      l = l.next;
    }

    if (l == null) return 0;
    else           return l.value;
  }





}




