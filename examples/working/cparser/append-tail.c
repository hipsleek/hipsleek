struct node {
  int val;
  struct node* next;
};

/*@
lseg2<p, n> == self=p & n=0
  or self::node<_, r> * r::lseg2<p, n-1>
  inv n>=0;

ll_tail2<tx, n> == self::node<_, null> & tx=self & n=1
  or self::node<_, r> * r::ll_tail2<tx, n-1> & r!=null
  inv self!=null & tx!=null & n>=1;

lemma "lseg2" self::lseg2<p, n> <- self::lseg2<q, n1>@D * q::lseg2<p, n2>@D & n=n1+n2;
lemma "ll_tail2" self::ll_tail2<t, n> <-> self::lseg2<t, n-1> * t::node<_, null>;
*/

void append(struct node* x, struct node* tx, struct node* y, struct node* ty)
/*@
  requires x::ll_tail2<tx, nnn> * y::ll_tail2<ty, mmm>
  ensures x::ll_tail2<ty, qqq> & qqq=mmm+nnn;
*/
{
  tx->next = y;
}
