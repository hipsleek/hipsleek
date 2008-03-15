class A {
	int a;
}

class B extends A {
	int b;
}

class C extends B {
	int c;
}


void f1(C x)
	static
	requires x::C<a,b,c>
	ensures x::A<a>;
{
}

void f2(C x)
	static
	requires x::A<a>
	ensures x::C<a,b,c>;
{
}

void f3(C x)
{
	assume x::C<a,b,c>;
	dprint;
	assert x::A$<a>;
}
