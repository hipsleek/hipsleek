public class CountUpRound{
  public static int round (int x) {

    if (x % 2 == 0) return x;
    else return x+1;
  }


  public static void main(String[] args) {
    Random.args = args;
    int x = Random.random();
    int y = Random.random();



    while (x > y) {

      y = round(y+1);

    }


  }

}
