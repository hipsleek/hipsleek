class A {
	int a;
	A b;	

	void m() {}

	A f() { return new A(1, null); }

	A f2(int a) { return null; }
}

void f() {
	A a = new A(10, null);

	dprint;

//	a.m();


//	a.b.f2(1);

//	a.f().b.b.f().m();
}
