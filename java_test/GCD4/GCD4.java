public class GCD4 {
  public static int mod(int a, int b) {
    while(a>=b && b > 0) {
      a -= b;
    }
    return a;
  }

  public static int gcd(int a, int b) {
    int tmp;
    while(b > 0 && a > 0) {
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
