data node2 {
	node2 prev;
	node2 next;	
}

dll<p,n> == self = null & n = 0 
  or self::node2<p , q> * q::dll<self, n-1> & n > 0;

void delete(node2 x, int a)
	requires x::dll<p, n> & n > a & a > 0 
	ensures x::dll<p, n-1>;
{
	if (a == 1){
		if (x.next.next != null)	{
      node2 tmp;
      x.next.next.prev = x;
      tmp = x.next.next;
			x.next = tmp;
		}
		else      
			x = null;
      // x.next = null;
	}
	else {
		delete(x.next, a-1);
	}
}

// RlPostAssign(node2 fr23_88 =  null)
// [RlFWrite x, next, fr23_88
// [RlFree [[node2 s92]]
// []]]
