data node {
  int val;
  node next;
}

pred ll<n> == self=null & n=0
  or self::node<_,q>*q::ll<n-1>
inv n>=0.

pred lseg<p,n> == self=p   & n=0
  or self::node<_,q>*q::lseg<p,n-1>
inv n>=0.

pred cll<n> == self::node<_,q>*q::lseg<self,n-1>
inv n>=1;

lemma_safe self::lseg<p,n> <- self::lseg<q,m>*q::node<_,p> & n=m+1.

/*int length(node xs)
  requires xs::cll<n>@L & Loop
  ensures false;
  requires xs::ll<n>@L & Term[n]
  ensures res=n;
{
  if (xs==null) return 0;
  else return 1+length(xs.next);
}
*/

node new_cll()
  requires emp
  ensures res::cll<_>;

node new_ll()
  requires emp
  ensures res::ll<_>;

int main()
{
  node xs = new_ll();
  int l = 0;
  while (true)
    requires xs::ll<n>@L & Term[n]
    ensures true;
  {
     if (xs == null)
       break;
     xs = xs.next;
     l = l+1;
  }
}

/* 
# ex1a-11.ss

   change to while loop & then C-code;
   write two diff main method
   can we also make use of non-determinisn
*/
