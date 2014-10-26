public class B extends A {
  public boolean hasSuperType() {
    return true;
  }

  public A getSuperType() {
    return new A();
  }
}
