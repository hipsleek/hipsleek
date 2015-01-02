public class MinusUserDefined{
  public static boolean gt(int x, int y) {

    while (x > 0 && y > 0) {
      x--;
      y--;
    }

    return x > 0;
  }


  public static void main(String[] args) {
    Random.args = args;
    int x = Random.random();
    int y = Random.random();
    int res = 0;

    while (gt(x,y)) {

      y++;
      res++;

    }
  }
}
