Array c1(int cap) 
	static 
	requires cap > 0
	ensures res::Array<cap>;
	dynamic
	requires cap > 0
	ensures res::Array<cap>$;
{
	Array tmp = new Array(cap);
	tmp.capacity = cap;
	return tmp;
}

class Array{
	int capacity;	
	inv capacity > 0;

	int get(int index) 
	static
	requires this::Array<c> & index >= 0 & index < c; 
	ensures this::Array<c>;
	dynamic
	requires this::Array<c>$ & index >= 0 & index < c; 
	ensures this::Array<c>$;	

	void set(int index, int val) 
	static
	requires this::Array<c> & index >=0 & index < c; 
	ensures this::Array<c>;
	dynamic
	requires this::Array<c>$ & index >=0 & index < c; 
	ensures this::Array<c>$;
}

List c2() 
	static
	requires true;
	ensures res::List<N, a># * a::Array<100> & N = 0;
	dynamic
	requires true;
	ensures res::List<N, a>$ * a::Array<100>$ & N = 0;
{
	Array a = c1(100);
	List tmp = new List(0, a);
	tmp.a = a;
	tmp.N = 0;
	return tmp;
}

class List {
	int N;
	Array a; 
	inv a::Array<c> & N >= 0 & N < c;
	
	void addtoList(int element)
	static
	requires this::List<N, a> * a::Array<c> & N < c
	ensures this::List<N+1, a> * a::Array<c>; 
	dynamic
	requires this::List<N, a>$ * a::Array<c>$ & N < c
	ensures this::List<N+1, a>$ * a::Array<c>$; 
	{
		
		this.a.set(this.N, element);
  		this.N = this.N + 1;
		return;
	}
	
	void main() {
        	List list = c2();
        	list.addtoList(4);
        	list.addtoList(2);
        	list.addtoList(1);
        	list.addtoList(3);
		//list.sortList();
		return;
	}

}
