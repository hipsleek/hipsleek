struct node {
	struct node* prev;
	struct node* next;
};

/*@
  dll<p,n> == self = null & n = 0
  or (exists q: self::node<p , q> * q::dll<self, n-1> & n > 0);
*/

void append(struct node* x, struct node* y)
/*@
  requires x::dll<p, n1> * y::dll<q, n2> & x!=null
  ensures x::dll<p, n1+n2>;
*/
{
	if (x->next == NULL){
    x->next = y;
    if (y != NULL) y->prev = x;
  } else {
    append(x->next, y);
  }

}
