public class TypeSwitch {
  public static void main(String[] args) {
    A x = null;
    switch (args.length) {
      case 0: x = new A();
              break;
      case 1: x = new B();
              break;
      case 2: x = new C();
              break;
    }

    while (x.hasSuperType()) {
      x = x.getSuperType();
    }
  }
}
