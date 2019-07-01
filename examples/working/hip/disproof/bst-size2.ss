data node2 {
	int val;
	node2 left;
	node2 right; 
}

bst <m, sm, lg> == self = null & sm <= lg & m = 0
	or (exists pl,qs: self::node2<v, p, q> * p::bst<m1, sm, pl> * q::bst<m2, qs,
	lg> & pl <= v & qs >= v &  m = 1 + m1 + m2)
	inv sm <= lg;

int size(node2 x)
    requires x::bst<size, sm, lg>
    ensures x::bst<size, sm, lg> & res = size;
{
  if (x != null) return 0;
  else {
       int cleft, cright;
       cleft = size(x.left);
       cright = size(x.right);
       return 1 + cleft + cright;
  }
}
