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

node new_node()
  requires emp
  ensures res::node<_,_>;

node new_ll(int n)
  requires n>=0
  ensures res::ll<n>;
{
  if (n==0)
    return null;
  node x = new_node();
  x.next = new_ll(n-1);
  return x;
}

void main()
  requires true
  ensures true;
{
  node xs = new_ll(10);
  while (true)
    requires xs::ll<n>@L & Term[n]
    ensures true;
  {
     if (xs == null)
       break;
     xs = xs.next;
  }
}

/* 
# ex1b2-11.ss

   change to while loop & then C-code;
   write two diff main method
   can we also make use of non-determinisn
*/
