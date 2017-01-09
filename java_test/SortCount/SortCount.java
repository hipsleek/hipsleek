public class SortCount{

  public static void main(String[] args) {
    Random.args = args;
    IntList l = IntList.createIntList();

    l = IntList.sort(0,l);

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

  public static boolean member(int n, IntList l) {
    while (l != null) {
      if (l.value == n) return true;
      else l =l.next;
    }

    return false;

  }

  public static int max(IntList l) {
    int m = 0;
    while (l !=null) {
      if (l.value > m) m = l.value;
      l = l.next;
    }
    return m;
  }


  public static IntList sort(int n, IntList l) {
    IntList res =null;
    while (max(l) >= n) {
      if (member(n,l)) res = new IntList(n,res);
      n++;
    }
    return res;
  }
}
