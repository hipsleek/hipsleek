/****************** class B ************************/
class B{
    	int x;
    	inv x >= 0;
    	int F(int i) 
	static
	requires this::B<_> & i >= 0
	ensures this::B<i> & res = i;
	dynamic
	requires this::B<_>$ & i >= 0
	ensures this::B<i>$ & res = i;
	{
		this.x = i;	
      		return this.x;
    	}
}


B c2() 
static
requires true
ensures res::B<0>;
dynamic
requires true
ensures res::B<0>$;
{
	B tmp = new B(0);
	tmp.x = 0;
	return tmp;
}


/****************** class C ************************/
class C extends B{
    	int y;
    	inv x < y;
    	
    	int F(int i) 
	static
	requires this::C<_, _> & i >= 0 
	ensures this::C<v, i> & i+1 <= v <= i+2 & res = v;
	dynamic
	requires this::C<_, _>$ & i >= 0 
	ensures this::C<v, i>$ & i+1 <= v <= i+2 & res = v;
	{ // overriding
        	this.x = i; 
        	if (this.x > 0) 
        		this.y = i+1;
        	else
        		this.y = i+2;		
      		return this.y;
    	}
}


C c1() 
static
requires true
ensures res::C<x, y>;
dynamic
requires true
ensures res::C<x, y>$;
{
	C tmp = new C(1, 0);		
	tmp.x = 0;
	tmp.y = tmp.x + 1;		//tmp.y = super.x + 1;
	return tmp;
}


/****************** class M ************************/
class M {
    	int ApplyFtoB(B b, int i)
	static 
	requires this::M<> * b::B<_> & i >= 0	 
	ensures this::M<> * b::B<i> & res = i;
	dynamic
	requires this::M<>$ * b::B<_>$ & i >= 0	 
	ensures this::M<>$ * b::B<i>$ & res = i;
	{ 
		return b.F(i); 
	}

    	int ApplyFtoC(C c, int i)
	static 
	requires this::M<> * c::C<_, _> & i >= 0	 
	ensures this::M<> * c::C<v, i> & i <= v <= i+1 & res = v;
	dynamic
	requires this::M<>$ * c::C<_, _>$ & i >= 0	 
	ensures this::M<>$ * c::C<v, i>$ & i <= v <= i+1 & res = v;
	{ 
		return c.F(i); 
	}

    	void Main() 
	static
	requires this::M<> 	
	ensures this::M<>;
	dynamic
	requires this::M<>$ 	
	ensures this::M<>$;
	{
      		B b = c2();
      		C c = c1();
		
		int arg = 3;
		int tmp1;
		int tmp2;
		int tmp3;
        	tmp1 = this.ApplyFtoB(b, arg);
        	tmp3 = this.ApplyFtoB(c, arg); 
        	tmp2 = this.ApplyFtoC(c, arg);
		return;
	}
}

