public class Collatz {
  public static void main(final int x) {
    int n = x;
    while (n > 1) {
      if (n % 2 == 0) {
        n = n / 2;
      } else {
        n = 3*n + 1;
      }
    }
  }

  public static void main(String[] args) {
    Random.args = args;
    main(Random.random());
  }
}
