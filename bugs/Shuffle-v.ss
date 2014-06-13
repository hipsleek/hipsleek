data node { int value; node next; }

lseg<n, p> ==
  self = p & n = 0 or
  self::node<v, q> * q::lseg<n-1, p> & self!=p
  inv n >= 0;

ll<n> ==
  self = null & n = 0 or
  self::node<v, q> * q::ll<n-1>
  inv n >= 0;


lemma_safe self::lseg<n,r>  <- self::lseg<m,q>*q::node<_,r> & n=m+1 ;


/*
// Binding error at (1)
node reverse (node l)
  requires l = null
  ensures res = null;
{
  if (l == null || l.next == null) return l; // (1)
  node nextItem = l.next;
  node reverseRest = reverse(nextItem);
  l.next = null;
  nextItem.next = l;
  return reverseRest;
}
*/

node reverse (node l)
 case { 
  l=null -> ensures res=l;
  l!=null -> 
   requires l::node<_,q> 
    case {
    q=null -> ensures l::node<_,null> & res=l ;
    q!=null -> 
      requires q::node<_,r>*r::lseg<n,null>
      ensures l::node<_,null> * res::lseg<n+1,l>;
    }
  }
/*
  requires l = null
  ensures res = l;  
  
  requires l::node<_, null>@L
  ensures res = l;
  
  requires l::node<_, p> * p::node<_, q> * q::lseg<n, null>
  case {
    q = null -> ensures p::node<_, l> * l::node<_, null> & res = p;
    q != null -> ensures res::lseg<_, _> * p::node<_, l> * l::node<_, null>;
  }
*/
{
  if (l == null) return l;
  if (l.next == null) return l;
  node nextItem = l.next;
  node reverseRest = reverse(nextItem);
  l.next = null;
  nextItem.next = l;
  //dprint;
  return reverseRest;
}
