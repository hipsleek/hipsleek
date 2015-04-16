public class Overflow {

  // does not terminate for any value of i
  public static void overflow(int i) {
    while(i <= 2147483647) {
      i++;
    }
  }

  public static void main(String[] args) {
    Random.args = args;
    overflow(Random.random());
  }
}
