struct node {
  int val;
  struct node* next;
};

/*@
ll<n> == self=null & n=0
  or self::node<_, q> * q::ll<n-1>
  inv n>=0;

relation A(int n, int m, int z).
*/

void append (struct node* x, struct node* y)
/*@
  infer [n,A]
  requires x::ll<n>*y::ll<m>
  ensures x::ll<z> & A(z,m,n);
*/
{
  struct node* tmp = x->next;
  if (tmp) {
    append(x->next, y);
    return;
  }
  else {
    x->next = y;
    return;
  }
};
