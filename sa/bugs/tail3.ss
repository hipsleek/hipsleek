data node{
	int val;
	node prev;
	node next;
}

node foo (node c, node y)
  requires c::node<_@A,_@M,n@L>
  ensures  c::node<_@A,y,_@A> & res=n;
{
   c.prev = y;
   return c.next;
}

  ll<n,a1,a2> == self=null & n=0
  or self::node<_@a1,q@a2>*q::ll<n-1,a1,a2>
  inv n>=0;



/*

 requires ll<n,a1,a2> & a1<:@M & a2<:I
 ensures  ll<n,a1,a2>;
 // length unchanged


 requires ll<n,a1,a2> & a1<:@I & a2<:I
 ensures  ll<n,a1,a2>;
 // nothing changed, better to use @L?
 // can preserve cut point?

 requires ll<n,a1,a2> & a1<:@I & a2<:M
 ensures  ll<n,a1,a2>;
 // elements not changed but list changed


 requires ll<n,@M,@v> & v<:I
 ensures  ll<n,@M,@v>;
 // length unchanged

node foo (node c, node y)
  requires c::ll<node<_@A,_@M,n@L>
  ensures  c::node<_@A,y,_@A> & res=n;
{
   c.prev = y;
   return c.next;
}


*/

