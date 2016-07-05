class Cnt {
	int val;

	void tick()
		static
			requires this::Cnt<v> ensures this::Cnt<v+1>;
		dynamic
			requires this::Cnt<v>$ ensures this::Cnt<w>$ & v+1<=w<=v+2;
	{
		this.val = 
				this.val + 1;
	}

	int get()
		static
		requires this::Cnt<v> ensures this::Cnt<v> & res=v;
		dynamic
		requires this::Cnt<v>$ ensures this::Cnt<v>$ & res=v;
	{
		return this.val;
	}

	void set(int x)
		static 
		requires this::Cnt<_> ensures this::Cnt<x>;
		dynamic
		requires this::Cnt<_>$ & x>=0 ensures this::Cnt<x>;
	{
		this.val = x;
	}		

	void f1() 
		static
			requires this::Cnt<v> ensures this::Cnt<v+1>;
		dynamic
			requires this::Cnt<v> ensures this::Cnt<w> & v+1<=w<=v+2;
	{
		this.tick();
	}
}


class FastCnt extends Cnt {
	void tick()
		static requires this::FastCnt<v> ensures this::FastCnt<v+2>;
		dynamic requires this::FastCnt<v>$ ensures this::FastCnt<v+2>$;
	{
		this.val = 
			this.val + 2;
	}
}


/*
void f()
{
	int a, b, c;
	a = b + c;
}
*/
