data node {
	int value;
	node next;
}

data queue {
	node first;
	node last;
}

data ring {
	int[] content; 	// buffer contents
    int size; 		// buffer capacity
    int first;  	// queue head
    int length; 	// queue length (maybe 0)
    node queue; 	// ghost queue for semantics proving
}

aqueue<f,l> == self = null & l = 0
	or self::node<v,n,l> * n::aqueue<_,l-1> & f = v

// list property not yet captured
buf<s,f,l> == self::ring<arr,s,f,l,q> * q::aqueue<f,l> & dom(arr,0,s-1) & 0<=l<=s & s>0 & 0<=f<s
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

int queuehead(ring b) {
	return b.content[b.first];
}

void queuepush(ring b, int x) 
	requires b::buf<s,f,l> & l < s
	ensures b::buf<s,f,l+1>;
{
	int p = (b.first + b.length) % b.size;
	b.content[p] = x;
	b.length = b.length + 1;
}

int queuepop(ring b)
	requires b::buf<s,f,l>
	ensures res = 0;
{
	int r = b.content[b.first];
	b.first = (b.first + 1) % b.size;
	b.length = b.length - 1;
	return r;
}

void test(int x, int y, int z) {
	ring b = create(2);
	queuepush(b, x);
	queuepush(b, y);
	int h = queuepop(b); assert h = x;
	queuepush(b, z);
	h = queuepop(b); assert h = y;
	h = queuepop(b); assert h = z;
}
