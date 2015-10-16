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

node new_lseg(node p, int n)
  requires n >=0
  ensures res::lseg<p,n>;
{
  if (n==0)
    return p;
  node x = new_node();
  x.next = new_lseg(p, n-1);
  return x;
}

node new_cll(int n)
  requires n>=1
  ensures res::cll<n>;
{
  node x = new_node();
  x.next = new_lseg(x,n-1);
  return x;
}

void main()
  requires true
  ensures false;
{
  int n = 10;
  node xs = new_cll(n);
  while (xs != null)
    requires xs::cll<n>@L & Loop
    ensures false;
  {
     xs = xs.next;
  }
}


/* 
# ex1b1-ll-while-loop-cll.ss

   change to while loop & then C-code;
   write two diff main method
   can we also make use of non-determinisn
*/
