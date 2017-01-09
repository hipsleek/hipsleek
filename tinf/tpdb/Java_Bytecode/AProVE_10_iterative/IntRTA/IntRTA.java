public class IntRTA {
  // only wrap a primitive int
  private int val;

  // count up to the value
  // in "limit"
  public static void count(
      IntRTA orig, IntRTA limit) {

    if (orig == null
        || limit == null) {
      return;
    }

    // introduce sharing
    IntRTA copy = orig;

    while (orig.val < limit.val) {
      copy.val++;
    }
  }

  public static void main(String[] args) {
    Random.args = args;
    IntRTA x = new IntRTA();
    x.val = Random.random();
    IntRTA y = new IntRTA();
    y.val = Random.random();
    count(x, y);
  }
}
