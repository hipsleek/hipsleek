public class PlusSwap{
  public static void main(String[] args) {
    Random.args = args;
    int x = Random.random();
    int y = Random.random();
    int z;
    int res = 0;

    while (y > 0) {

      z = x;
      x = y-1;
      y = z;
      res++;

    }

    res = res + x;
  }
}
