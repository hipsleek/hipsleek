public class LoopingNonterm {
 public static void main(String[] a) {
  int i = 0;
  int j = a.length;
  while (i < j) {
   i += a[i].length();
  }
 }
}
