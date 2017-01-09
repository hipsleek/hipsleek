public class NonPeriodicNonterm2 {
  public static void main(String[] args) {
   int x = args[0].length(); 
   int y = args[1].length();
   while(x >= y) {
    int z = x - y;
    if (z > 0) {
     x--;
    } else {
     x = 2*x + 1;
     y++;
    }
   }
  }
}
