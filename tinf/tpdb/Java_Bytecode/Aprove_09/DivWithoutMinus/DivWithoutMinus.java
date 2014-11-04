public class DivWithoutMinus{
  // adaption of the algorithm from [Kolbe 95]
  public static void main(String[] args) {
    Random.args = args;

    int x = Random.random();
    int y = Random.random();
    int z = y;
    int res = 0;

    while (z > 0 && (y == 0 || y > 0 && x > 0))	{

      if (y == 0) {
        res++;
        y = z;
      }
      else {
        x--;
        y--;
      }
    }
  }
}

