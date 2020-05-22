struct node {
  int val;
  struct node* next;
};

/*@
  ll<n> == self=null & n = 0
  or self::node<_, r> * r::ll<n2> & n = 1 + n2
  inv n >= 0;
*/

void delete(struct node* x, int a)
/*@
  requires x::ll<n> & n > a & a > 0 
	ensures x::ll<n - 1>;
*/
{
  if (a == 1)
    {
      x -> next = x -> next -> next;
    }
	else {
		delete(x -> next, a - 1);
	}
}
