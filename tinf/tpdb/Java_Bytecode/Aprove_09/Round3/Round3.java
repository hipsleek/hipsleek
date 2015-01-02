public class Round3{
  public static void main(String[] args) {
    Random.args = args;
    int x = Random.random();

    while (x % 3 != 0) {
      x++;
    }
  }
}
