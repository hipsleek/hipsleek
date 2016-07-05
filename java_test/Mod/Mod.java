public class Mod {
  public static void main(String[] args) {
    int x = args[0].length();
    int y = args[1].length();
    mod(x, y);
  }
  public static int mod(int x, int y) {
   
    while (x >= y && y > 0) {
      x = minus(x,y);
     
    }
    return x;
  }

  public static int minus(int x, int y) {
    while (y != 0) {
      if (y > 0)  {
        y--;
        x--;
      } else  {
        y++;
        x++;
      }
    }
    return x;
  }

}
