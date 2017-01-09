struct node {
  int val;
  struct node * next;
};

struct node* main(struct node* l)
/*@
 requires l::node<_,_>
  ensures res::node<_,_>;
*/
{
  return l;
}
