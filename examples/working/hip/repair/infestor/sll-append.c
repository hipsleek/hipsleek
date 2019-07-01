struct node {
  int val;
	struct node* next;
};

/*@
ll<n> == self = null & n = 0
	or self::node<_, q> * q::ll<n-1>;
*/

void append(struct node* x, struct node* y)
/*@
  requires x::ll<n1> * y::ll<n2> & x!=null
  ensures x::ll<n1+n2>;
*/
{
	if (x->next == NULL){
      x->next = y;
  } else {
    append(x->next, y);
  }

}
