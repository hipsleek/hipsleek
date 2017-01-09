public class McCarthyIterative {
  public static int main(int x) {
    int c = 1;
    while (c > 0) {
      if (x > 100) {
        x -= 10;
        c--;
      } else {
        x += 11;
        c++;
      }
    }
    return x;
  }

  public static void main(String[] args) {
    Random.args = args;
    main(Random.random());
  }
}
