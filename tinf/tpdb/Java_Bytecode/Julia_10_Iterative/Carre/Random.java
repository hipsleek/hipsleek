public class Random {
  static String[] args;
  static int index = 0;

  public static int random() {
      if (index >= args.length)
	  return 0;

      String string = args[index];
      index++;
      return string.length();
  }
}
