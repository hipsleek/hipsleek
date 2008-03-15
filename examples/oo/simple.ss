class A{
	int a;
	inv a >= 0;	

	int get()
	static 
	requires this::A<a>
	ensures this::A<a> & res = a;
	dynamic
	requires this::A<a>$
	ensures this::A<a>$ & res = a;
	{
	return this.a;
	}
	
	void set(int v)
	static
	requires this::A<_># & v >= 0
	ensures this::A<v>#;
	dynamic
	requires this::A<_>$ & v >= 0
	ensures this::A<v>$;
	{
	this.a = v;
	}

}

class B extends A{
	inv a > 0;
	
	void set(int v)
	static
	requires this::B<_> /*& v >= 0*/
	ensures this::B<v>;
	dynamic
	requires this::B<_>$ /*& v >= 0*/
	ensures this::B<v>$;
	{
	this.a = v;
	}
	
}

class M {
	void main(B x) 
	static 
	requires this::M<> * x::B<a>
	ensures true;
	dynamic
	requires this::M<>$ * x::B<a>$
	ensures true;
	{
	int tmp = x.get();	
	}
	
}
