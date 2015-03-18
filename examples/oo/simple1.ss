A c1() 
static
requires true
ensures res::A<0>;
dynamic
requires true
ensures res::A<0>$;
{
	A tmp = new A(0);
	return tmp;

}

class A{
	int a;
}


B c2()
static
requires true;
ensures res::B<a, 0> * a::A<_>;
dynamic
requires true;
ensures res::B<a, 0>$ * a::A<_>$;
{
	B tmp;
	A tmp1 = c1();
	tmp = new B(tmp1, 0);
	tmp.a = tmp1;
	tmp.b = 0;
	return tmp;
}

class B{
	A a;
	int b;
}
