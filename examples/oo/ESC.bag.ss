/* 
	this example appears both in JavaESC and Spec#
*/


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

Bag c2(Array a) 
	static
	requires a::Array<c>
	ensures res::Bag<a1, 0> * a1::Array<c> & a1 = a;
	dynamic
	requires a::Array<c>$
	ensures res::Bag<a1, 0>$ * a1::Array<c>$ & a1 = a;
{
	Bag tmp = new Bag(a, 0);
	tmp.a = a;
	return tmp;
}

class Bag {
  Array a;
  int n;
  inv a::Array<c> & 0 <= n & n < c;

  	int extractMin()
	static 
	requires this::Bag<a, n> * a::Array<c> & n >= 1
	ensures this::Bag<a, n-1> * a::Array<c>;
	dynamic
	requires this::Bag<a, n>$ * a::Array<c>$ & n >= 1
	ensures this::Bag<a, n-1>$ * a::Array<c>$;
  	{
 	int i = 1;	
    	int m = this.a.get(0);
    	int mindex = 0;
    	while (i <= this.n) {
      		if (this.a.get(i) < m) {
        		mindex = i;
        		m = this.a.get(i);
      		}
		i = i+1;
    	}
    	this.n--;
    	this.a.set(mindex, this.a.get(this.n));
    	return m;
  	}
  

  	void add(int x) 
	static
	requires this::Bag<a, n> * a::Array<c>
	ensures this::Bag<a, n+1> * a::Array<c> or
	this::Bag<a, n+1> * a::Array<c1> & c1 = c + c;  
	dynamic
	requires this::Bag<a, n>$ * a::Array<c>$
	ensures this::Bag<a, n+1>$ * a::Array<c>$ or
	this::Bag<a, n+1> * a::Array<c1> & c1 = c + c;  
	{
	int i;
      	if (this.a.capacity == this.n+1)		// array full
      	{
		Array new_a = c1(2 * this.a.capacity);	// double the capacity
	      	i = 0;
		while (i <=  this.n) {			// copy a into a_new
			new_a.set(i, this.a.get(i));
			i = i+1;
		}
	 
		this.a = new_a;
     	}
	this.n++;
	this.a.set(this.n, x);
  	}
  
}


