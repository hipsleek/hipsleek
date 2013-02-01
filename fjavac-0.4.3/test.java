// -*- compile-command: "make javacx && ./javacx -v test.java" -*-

class C extends Object { 
  C x;
  C f () { return this.x; }
}

class D extends C { 
  D y;
//  C f (C c) { return new C(); } // override error
//  D f () { return new D(); } // override error
//  C g1 () { return this.z; } // unbound field
  C g1 () { return new D(); }
//  C g2 () { return this.f(); }
  C g3 (C c, D d) { return d; }
}
