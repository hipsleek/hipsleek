
data ring {
	int[] content; // buffer contents
	int size; // buffer capacity
	int first;  // queue head
	int length; // queue length (maybe 0)
}


// list property not yet captured
buf<s,f,l,arr> == 
  self::ring<arr,s,f,l> & dom(arr,0,s-1) & 0<=l<=s & s>0 & 0<=f<s 
  inv s>=1 & 0<=l<=s;

ring create(int n)
	requires n>0
  ensures res::buf<n,0,0,_>;
{
	int[] a = new int[n];
	return new ring(a,n,0,0);
}

void clear(ring b)
    requires b::buf<s,f,l,a>
    ensures b::buf<s,f,0,_>;
{
	b.length = 0;
}

// assumes that b is not empty
int queuehead(ring b) 
  requires b::buf<s,f,l,a> & l>0
  ensures b::buf<s,f,l,a> & res=a[f]; 
{
	return b.content[b.first];
}

int cyclic_inc(int x, int b)
 requires 0<=x<b
 case {
  x+1=b -> ensures res=0;
  x+1!=b -> ensures res=x+1;
 }


int cyclic_add(int f, int l, int s)
 requires 0<=l<s & 0<=f<s
 case {
  f+l<s -> ensures res=f+l;
  f+l>=s -> ensures res=f+l-s;
 }


// assumes that b is not full
void queuepush(ring b, int x) 
  requires b::buf<s,f,l,a> & l < s
  case {
    f+l<s -> ensures b::buf<s,f,l+1,a1>
         & update_array_1d(a,a1,x,f+l); 
   f+l>=s -> ensures b::buf<s,f,l+1,a1>
         & update_array_1d(a,a1,x,f+l-s);
  }
{
    //int p = (b.first + b.length) % b.size;
    int p = cyclic_add(b.first,b.length,b.size);
	b.content[p] = x;
	b.length = b.length + 1;
}



// assumes that b is non-empty
int queuepop(ring b)
  requires b::buf<s,f,l,a> & l>0
    case {
       f=s-1 -> 
         ensures b::buf<s,0,l-1,a> & res=a[s-1]; 
       f!=(s-1) -> 
         ensures b::buf<s,f+1,l-1,a> & res=a[f];
    }
{
  if (b.length==0) return 0;
  else {
	int r = b.content[b.first];
	//b.first = (b.first + 1) % b.size;
    b.first = cyclic_inc(b.first,b.size);
	b.length = b.length - 1;
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
    assert h' = x';
	queuepush(b, z);
	h = queuepop(b); 
    assert h' = y';
	h = queuepop(b); 
    assert h' = z';
}


