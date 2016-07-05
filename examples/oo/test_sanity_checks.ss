class A {
	int a;
	A b;	
	A a;

	void m() {}

	A f() { return new A(1, null); }

	A f(int a) { return null; }
}

class B extends A {
	int a;
	A g(int a) { return new A(1, null); }
}

class D extends B {
	A a;
	A g() { return new A(1, null); }
}

class E extends D {
	A a;
	A g() { return new A(1, null); }
}

class C {
	A f() { return new A(1, null); }
	void m(int n) {}
}

void f() {
	A a = new A(10, null);

	a.m();


	a.b.f2(1);

	a.f().b.b.f().m();
}
