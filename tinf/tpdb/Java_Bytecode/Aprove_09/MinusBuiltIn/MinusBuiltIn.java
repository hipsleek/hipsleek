public class MinusBuiltIn{

  public static void main(String[] args) {
    Random.args = args;
    int x = Random.random();
    int y = Random.random();
    int res = 0;



    while (x > y) {

      y++;
      res++;

    }
  }

}

