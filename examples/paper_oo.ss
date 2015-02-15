class Cnt {
	int val;

	Cnt cnt(int v)
	static
	requires true ensures res::Cnt<v>;
	{
		Cnt ths = new Cnt(0);
		ths.val = v;
		return ths;
	}
	
	void tick()
	static			
	requires this::Cnt<v> ensures this::Cnt<v+1>;
	dynamic
	requires this::Cnt<v>$ ensures this::Cnt<w>$ & v+1<=w<=v+2;
	{
		this.val = this.val + 1;
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
	requires this::Cnt<_> 
	ensures this::Cnt<x>;
	dynamic
	requires this::Cnt<_>$ & x>=0 
	ensures this::Cnt<x>$;
	{
		this.val = x;
	}		
}


class PosCnt extends Cnt {
	inv val >= 0;
	
	PosCnt posCnt(int v)
	static
	requires v >= 0
	ensures res::PosCnt<v> & v >= 0;
	{
		PosCnt ths = new PosCnt(0);
		ths.val = v;
		return ths;
	}

	void tick()
	static
	requires this::PosCnt<v> & v >= 0 
	ensures this::PosCnt<v+1> & v+1 >= 0;

	int get()
	static
	requires this::PosCnt<v> & v >= 0
	ensures this::PosCnt<v> & v >= 0 & res=v;

	void set(int x)
	static
	requires this::PosCnt<_> & x >= 0 
	ensures this::PosCnt<x> & x >= 0;
	{
		this.val = x; 
	}

}

class FastCnt extends Cnt {
	/*FastCnt fastCnt(int v)
	static
	requires true
	ensures res::FastCnt<v>;
	{
		this = new FastCnt(0);
		this.val = v;
		return this;	}*/

	void tick()
	static 
	requires this::FastCnt<v> ensures this::FastCnt<v+2>;
	{
		this.val = this.val + 2;
	}
}

class TwoCnt extends Cnt {
        int bak;
        
	/*TwoCnt twoCnt(int v, int b) 
	static
	requires true
	ensures res::TwoCnt<v,b>;
	{
		this = new TwoCnt(0,0);
		this.val = v;
		this.bak = b;
		return this;
	}*/


        void set(int x)
        static
        requires this::TwoCnt<v, _>
        ensures this::TwoCnt<x, v>;
	{
		this.bak = this.val;
		this.val = x;
	}
	void switch(int x) 
	static
	requires this::TwoCnt<v,b>
	ensures this::TwoCnt<b,v>;
	{
		int i = this.val;
		this.val = this.bak;
		this.bak = i;
	}
}

class ThreeCnt extends TwoCnt {
	int cak;
	
	/*ThreeCnt threeCnt(int v, int b, int c)
	static
	requires true
	ensures res::ThreeCnt<v, b, c>;
	{
		this = new ThreeCnt(0,0,0);
		this.val = v;
		this.bak = b;
		this.cak = c;
		return this;
	}*/

	void set(int x)
	static
	requires this::ThreeCnt<v,b,_>
	ensures this::ThreeCnt<x,v,b>;
	{
		this.cak = this.bak;
		this.bak = this.val;
		this.val = x;
	}
}
