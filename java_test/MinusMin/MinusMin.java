public class MinusMin{

  public static int min (int x, int y) {

    if (x < y) return x;
    else return y;
  }


  public static void main(String[] args) {
    Random.args = args;
    int x = Random.random();
    int y = Random.random();
    int res = 0;



    while (min(x-1,y) == y) {

      y++;
      res++;

    }


  }

}
