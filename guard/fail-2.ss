data node {
  node next;
}

ll<n> == self=null & n=0
  or self::node<q>*q::ll<n-1>
  inv n>=0;

ls<p,n> == self=p & n=0
  or self::node<q>*q::ls<p,n-1> & self!=p
  inv n>=0;


lemma_safe self::ls<p,n> & a+b=n & a>=0 & b>=0 
  <- self::ls<r,a>*r::ls<p,b>;


void loop(node@R l1, node@R l2) 
  requires (l2::ls<null,n>@L & l1::ls<q,n-1>@L) & n>0   
  ensures l2'=null & l1'=q;
{
  l2=l2.next;
  if (l2==null) return;
  else {l1=l1.next;
    loop(l1,l2);
  };
}

void foo(node list) 
  requires list::ls<null,m> & m>1
  ensures true;
{
  node l1= list;
  node l2= list.next;
  dprint;
  loop(l1,l2);
  l2 = l1.next;
}
