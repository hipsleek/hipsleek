package SharingAnalysis;

public class Random {
  static String[] args;
  static int index = 0;

  public static int random() {
    final String string = args[index];
    index++;
    return string.length();
  }
}
