struct node2 {
	int val;
	struct node2 *prev;
	struct node2 *next;
};

/*@
dll<p,n> == self = null & n = 0
  or self::node2<_ ,p , q> * q::dll<self, n-1> // = q1
	inv n >= 0;

relation D(int x, int y, int z, node2 m, node2 n, node2 p).
*/

void append2(struct node2* x, struct node2* y)
/*@
  infer  [D]
	requires x::dll<q, m> * y::dll<p, n> & m>=1
	ensures x::dll<r, t> & D(t,m,n,r,p,q);
*/
{
	struct node2* tmp;
	if (x->next == NULL) {
		x->next = y;
		if (y != NULL) {
			y->prev = x;
		}
	}
	else {
		append2(x->next, y);
	}
}
