struct node {
  int val;
  struct node* next;
};

/*@
ll<n> == self=null & n = 0
  or self::node<_, r> * r::ll<n2> & n = 1 + n2;
*/

int length(struct node* x)
/*@
  requires x::ll<n>
  ensures x::ll<n> & res = n;
*/
{
  if (x == NULL) return 0;
  else {
    int k;
    k = 1 + length(x->next);
    return k;
  }
}
