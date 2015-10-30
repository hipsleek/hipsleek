struct node {
  int val;
  struct node* next;
};

/*@
ll<n> == self=null & n=0
  or self::node<_,q>*q::ll<n-1>
inv n>=0.

lseg<p,n> == self=p   & n=0
  or self::node<_,q>*q::lseg<p,n-1>
inv n>=0.

cll<n> == self::node<_,q>*q::lseg<self,n-1>
inv n>=1;

lemma_safe self::lseg<p,n> <- self::lseg<q,m>*q::node<_,p> & n=m+1.

*/

int length(struct node* xs)
  /*@
     requires xs::cll<n>@L & Loop
     ensures false;
     requires xs::ll<n>@L & Term[n]
     ensures res=n;
  */
{
  if (xs == NULL) 
    return 0;
  return (1+length(xs->next));
}

