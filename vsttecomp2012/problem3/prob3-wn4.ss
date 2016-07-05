// Problem 3 
//   1. Proven array access are within bounds of allocated array
//   2. Proven FIFO behavior of queue by modelling the elements
//      in the array
//   3. Proven test harness

data ring_buffer {
	int[] content; // buffer contents
	int size; // buffer capacity
	int first;  // queue head
	int length; // queue length (maybe 0)
}


// this predicate captures the field invariant for s,f,l 
// and memory allocation done for the array through dom(arr,0,s-1)
// which denotes that we have an array allocated from index 0 to s-1
buf<s,f,l,arr> == 
  self::ring_buffer<arr,s,f,l> & dom(arr,0,s-1) & 0<=l<=s & s>0 & 0<=f<s 
  inv s>=1 & 0<=l<=s;

// buffer size >=1
ring_buffer create(int n)
	requires n>0
    ensures res::buf<n,0,0,_>;
{
	int[] a = new int[n];
	return new ring_buffer(a,n,0,0);
}

void clear(ring_buffer b)
    requires b::buf<s,f,l,a>
    ensures b::buf<s,f,0,_>;
{
	b.length = 0;
}

// precondition : b must be non-empty
int queuehead(ring_buffer b) 
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


// precondition : b is not full
void queuepush(ring_buffer b, int x) 
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

// precondition : b is non-empty
int queuepop(ring_buffer b)
  requires b::buf<s,f,l,a> & l>0
    case {
       f=s-1 -> 
         ensures b::buf<s,0,l-1,a> & res=a[f]; 
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
	ring_buffer b = create(2);
	queuepush(b, x);
	queuepush(b, y);
	int h = queuepop(b);
    // note that v denotes the original value
    // at declaration or method entry, while v' 
    // v' denotes the latest values of each variable/parameter 
    assert h' = x';
	queuepush(b, z);
	h = queuepop(b); 
    assert h' = y';
	h = queuepop(b); 
    assert h' = z';
}

