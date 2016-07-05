data node2 {
	int val;
	node2 left;
	node2 right; 
}

bst3 <n,h, sm, lg,S> == self = null & sm <= lg & n = 0 & h = 0 & S={}
  or (exists pl,qs: self::node2<v, p, q> * p::bst3<n1,h1,sm, pl,S1> *
      q::bst3<n2,h2,qs, lg,S2> & pl <= v & qs >= v & n=n1+n2+1 & h=1+max(h1,h2)
      & S=union(S1,S2,{v}))
	inv h >= 0 & n >= 0 & sm <= lg;

/* view for a doubly linked list with size */
dll<p, n,S> == self = null & n = 0 & S={}
  or self::node2<v, p, q> * q::dll<self, n1,S1> & n = n1+1 & S=union(S1,{v})
	inv n >= 0;


node2 append1(node2 x, node2 y)
  requires x::dll<_, m,S1> * y::dll<_, n,S2>
  ensures res::dll<r, m+n,S> & S=union(S1,S2);


void flatten_ok(node2 x)
  requires x::bst3<n,h,sm, lg,S1>
  ensures x::dll<q, n,S2> & q=null & S1=S2;
{
  node2 tmp;
  if (x != null)
	{
      flatten_ok(x.left);
      flatten_ok(x.right);
      tmp = append1(x.left, x.right);
      x.left = null;
      x.right = tmp;
      if (tmp != null)
        tmp.left = x;
	}
}

relation FLAT1(bag x, bag y).
void flatten_fail1(node2 x)
  infer[FLAT1]
  requires x::bst3<n,h,sm, lg,S1>
  ensures x::dll<q, n,S2> & q=null & S1=S2;//;FLAT(S1,S2);//S1=S2;
{
  node2 tmp;
  if (x != null)
	{
      flatten_fail1(x.left);
      flatten_fail1(x.right);
      tmp = append1(x.left, x.right);
      x.left = null;
      x.right = tmp;
      if (tmp != null)
        tmp.left = x;
	}
}

relation FLAT(bag x, bag y).
void flatten_fail2(node2 x)
  infer[FLAT]
  requires x::bst3<n,h,sm, lg,S1>
  ensures x::dll<q, n,S2> & q=null & FLAT(S1,S2);//S1=S2;
{
  node2 tmp;
  if (x != null)
	{
      flatten_fail2(x.left);
      flatten_fail2(x.right);
      tmp = append1(x.left, x.right);
      x.left = null;
      x.right = tmp;
      if (tmp != null)
        tmp.left = x;
	}
}
