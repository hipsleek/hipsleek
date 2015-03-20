public class GCD2 {
  public static int mod(int a, int b) {
    if (a == b) {
      return 0;
    }
    while(a>b) {
      a -= b;
    }
    return a;
  }

  public static int gcd(int a, int b) {
    int tmp;
    while(b != 0 && a >= 0 && b >= 0) {
      tmp = b;
      b = mod(a, b);
      a = tmp;
    }
    return a;
  }

  public static void main(String[] args) {
    Random.args = args;
    int x = Random.random();
    int y = Random.random();
    gcd(x, y);
  }
}
