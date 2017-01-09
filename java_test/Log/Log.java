public class Log{
  public static int half(int x) {

    int res = 0;

    while (x > 1) {

      x = x-2;
      res++;

    }

    return res;

  }


  public static int log(int x) {

    int res = 0;

    while (x > 1) {

      x = half(x);
      res++;

    }

    return res;

  }


  public static void main(String[] args) {
    Random.args = args;
    int x = Random.random();
    log(x);
  }
}
