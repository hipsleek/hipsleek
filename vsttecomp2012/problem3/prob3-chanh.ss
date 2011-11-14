data ring {
	int[] content; // buffer contents
	int size; // buffer capacity
	int first;  // queue head
	int length; // queue length (maybe 0)
}


// list property not yet captured
buf<s,f,l> == 
  self::ring<arr,s,f,l> & dom(arr,0,s-1) & 0<=l<=s & s>0 & 0<=f<s
  inv s>=1 & 0<=l<=s;

ring create(int n)
	requires n>0
	ensures res::buf<n,0,0>;
{
	int[] a = new int[n];
	return new ring(a,n,0,0);
}

void clear(ring b)
	requires b::buf<s,f,l>
	ensures b::buf<s,f,0>;
{
	b.length = 0;
}

// assumes that b is not empty
int queuehead(ring b) 
	requires b::buf<s,f,l> & l>0
    ensures b::buf<s,f,l>; 
{
	return b.content[b.first];
}



// assumes that b is not full
void queuepush(ring b, int x) 
	requires b::buf<s,f,l> & l < s
	ensures b::buf<s,f,l+1>;
{
	int p = (b.first + b.length) % b.size;
	b.content[p] = x;
	b.length = b.length + 1;
}

int cyclic_inc(int x, int b)
 requires 0<=x<b
 case {
  x+1=b -> ensures res=0;
  x+1!=b -> ensures res=x+1;
 }

// assumes that b is non-empty
// redlog needed to prove with mod operator
int queuepop(ring b)
	requires b::buf<s,f,l> & l>0
    case {
       f=s-1 -> 
         ensures b::buf<s,0,l-1>; 
       f!=(s-1) -> 
         ensures b::buf<s,f+1,l-1>;
    }
{
  if (b.length==0) return 0;
  else {
	int r = b.content[b.first];
    //b.first = cyclic_inc(b.first,b.size);
	//assert b.fisrt < b.size; //loop
	//int modb = (b.first + 1) % b.size;
	b.first = (b.first + 1) % b.size;
	//b.first = modb;
	b.length = b.length - 1;
    //assume false;
	return r;
  }
}

void test(int x, int y, int z) 
  requires true
  ensures true;
{
	ring b = create(2);
	queuepush(b, x);
	queuepush(b, y);
	int h = queuepop(b); 
    //assert h = x;
	queuepush(b, z);
	h = queuepop(b); 
    //assert h = y;
	h = queuepop(b); 
    //assert h = z;
}
