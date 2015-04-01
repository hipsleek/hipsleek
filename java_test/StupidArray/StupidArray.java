public class StupidArray {
  public static void main(String[] args) {
    int i = 0;
    while (true) {
      i = args.length + 1;
      args[i] = new String();
    }
  }
}

