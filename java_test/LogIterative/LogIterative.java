public class LogIterative {
  public static int log(int x, int y) {
    int res = 0;
    while (x >= y && y > 1) {
      res++;
      x = x/y;
    }
    return res;
  } 

  public static void main(String[] args) {
    Random.args = args;
    int x = Random.random();
    int y = Random.random();
    log(x, y);
  }
}
