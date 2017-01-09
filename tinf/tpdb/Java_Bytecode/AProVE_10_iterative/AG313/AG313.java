public class AG313 {
  public static void main(String[] args) {
    int x, y;
    x = args[0].length();
    y = args[1].length() + 1;
    quot(x,y);

  }


  public static int quot(int x, int y) {
    int i = 0;
    if(x==0) return 0;
    while (x > 0 && y > 0) {
      i += 1;
      x = (x - 1)- (y - 1);

    }
    return i;
  }
}
