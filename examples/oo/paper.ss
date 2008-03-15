class Cnt {
	int val;
	/*Cnt(int v)
	static
		requires true ensures this::Cnt<v>
	{
		this.val = v;
	}*/
	
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
	
	/*PosCnt(int v)
	static
	requires v >= 0
	ensures res::PosCnt#;
	{
		this.val = v;
	}*/

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
	/*FastCnt(int v)
	static
	requires true
	ensures res::FastCnt<v>;
	{
		this.val = v;
	}*/

	void tick()
	static 
	requires this::FastCnt<v> ensures this::FastCnt<v+2>;
	{
		this.val = this.val + 2;
	}
}

class TwoCnt extends Cnt {
        int bak;
        
	/*TwoCnt(int v, int b) 
	static
	requires true
	ensures res::TwoCnt<v,b>;
	{
		this.val = v;
		this.bak = b;
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
	
	/*ThreeCnt(int v, int b, int c)
	static
	requires true
	ensures res::ThreeCnt<v, b, c>;
	{
		this.val = v;
		this.bak = b;
		this.cak = c;
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
