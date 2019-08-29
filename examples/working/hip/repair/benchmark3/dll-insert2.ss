data node2 {
	int val; 
	node2 prev;
	node2 next;	
}

/* view for a doubly linked list with size */
dll<p,n> == self = null & n = 0 
  or self::node2<_ ,p , q> * q::dll<self, n-1> & n > 0;

void insert(node2 x, int a)
  requires x::dll<p, n> & n>0
  ensures x::dll<p, n+1>; 
{
  if (x.next == null)
      x.next = new node2(a, x.next, null);
      // x.next = new node2(a, x, null);
	else
      insert(x.next, a);
}

// RlMkNull node2 f_r_88,  null
// [RlAllocate node2([[int a,node2 x,node2 f_r_88]])
// [RlFrameData(node2 q_78, node2 f_r_92)
// [RlFWrite x, next, f_r_92
// [RlSkip
// []]]]]
