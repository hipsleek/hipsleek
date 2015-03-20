public class DivMinus {
  public static int div(int x, int y) {
    int res = 0;
    while (x >= y && y > 0) {
      x = x-y;
      res = res + 1;
    }
    return res;
  }

  public static void main(String[] args) {
    Random.args = args;
    int x = Random.random();
    int y = Random.random();
    div(x, y);
  }
}
