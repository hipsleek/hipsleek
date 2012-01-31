// Problem 3 
//   1. Verified array access are within bounds of allocated array
//   2. Verified FIFO behavior of queue by modelling the elements
//      as a sequence in the circular array
//   3. Verified test harness

data ring_buffer {
	int[] content; // buffer contents
	int size; // buffer capacity
	int first;  // queue head
	int length; // queue length (maybe 0)
}

// this predicate captures the field invariants for s,f,l 
// and memory allocation done for the array through dom(arr,0,s-1)
// which denotes that we have an array allocated from index 0 to s-1
buf<s,f,l,arr> == 
  self::ring_buffer<arr,s,f,l> & dom(arr,0,s-1) & 0<=l<=s & s>0 & 0<=f<s 
  inv s>=1 & 0<=l<=s & 0<=f<=s;

// precondition : n>=1 to create buffer with size>=1 
// postcondition : buffer contains allocated
//    array with unknown values 
ring_buffer create(int n)
	requires n>0
    ensures res::buf<n,0,0,_>;
{
	int[] a = new int[n];
	return new ring_buffer(a,n,0,0);
}

// postcondition : buffer contains allocated
//    array with unknown values 
void clear(ring_buffer b)
    requires b::buf<s,f,l,a>
    ensures b::buf<s,f,0,_>;
{
	b.length = 0;
}

// precondition : b must be non-empty
// postcondition : buffer is unchanged, and
//    res is first element of queue
int queuehead(ring_buffer b) 
  requires b::buf<s,f,l,a> & l>0
  ensures b::buf<s,f,l,a> & res=a[f]; 
{
	return b.content[b.first];
}


// precondition : b is not full
// postcondition : queue has one more
//    element added to its end
void queuepush(ring_buffer b, int x) 
  requires b::buf<s,f,l,a> & l < s
  case {
    f+l<s -> ensures b::buf<s,f,l+1,a1>
         & update_array_1d(a,a1,x,f+l); 
   f+l>=s -> ensures b::buf<s,f,l+1,a1>
         & update_array_1d(a,a1,x,f+l-s);
  }
{
    int p = (b.first + b.length) % b.size;
	b.content[p] = x;
	b.length = b.length + 1;
}

// precondition : b is non-empty
// postcondition : queue has one less
//    element removed from its front
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
	b.first = (b.first + 1) % b.size;
	b.length = b.length - 1;
	return r;
  }
}


// test harness where valid assertions
// are checked
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

