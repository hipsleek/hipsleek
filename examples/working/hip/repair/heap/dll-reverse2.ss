data node2 {
  node2 prev;
  node2 next;
}

dll<pr, n> == emp & self=null & n = 0
  or self::node2<pr,q>*q::dll<self, n2> & n = n2 + 1;

// node reverse(node2 x)
// requires x::dll<pr, n> & pr = null;
// ensures res::dll<pr2, n> & pr2 = null;
// {
//   if (x== null) return null;
//   else if (x.next == null) return x;
//   else {
//     node2 k;
//     k = reverse(x.next);
//   }
// }


void reverse(node@R xs, node@R ys)
	requires xs::ll<n> * ys::ll<m> 
	ensures ys'::ll<n+m> & xs' = null;
{
	if (xs != null) {
		node tmp;
		tmp = xs.next;
		xs.next = ys;
		ys = xs;
		xs = tmp;
		reverse(xs, ys);
	}
}
