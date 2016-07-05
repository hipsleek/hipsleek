
struct node{
  int val;
  struct node* next;
};

/*@
ll_inf<> == self::node<1,q>*q::ll_inf<>
inv true.


*/

int check(struct node* xs)
  /*@
     requires xs::ll_inf<>@L & Loop
     ensures false;
     requires xs::node<0,p>@L * p::ll_inf<>@L & Term
     ensures res=1;
*/
{
  if (xs->val == 0)
    return 1;
  return check(xs->next);
}

