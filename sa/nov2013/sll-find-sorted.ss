
data node {
 int val;
 node next;
}

HeapPred H(node x, int v). // non-ptrs are @NI by default
  PostPred G(node x, int v). // non-ptrs are @NI by default

  sortll<n:int> == self=null
  or self::node<v,q>*q::sortll<v> 
     & n<=v 
& self!=null
 inv true; 

bool find_sorted(node x, int v)
  infer [H,G]
  requires H(x,v)
     ensures G(x,v);
//requires x::sortll<v>@L ensures  res;
/*
 requires x::sll2<n, sm, lg>
  ensures res::sll2<n, mi, ma> & mi=min(v, sm) & ma=max(v, lg);// ma=max(v, lg)
 */
{ 
  if (x==null) return false;
  else {
    if (x.val==v) return true;
   else {
     if (x.val<v) return false;
     else
       return find_sorted(x.next,v);;
   }
 }
} 

/*
# check-sorted.ss --sa-en-pure-field --sa-dnc

[ H(x,v) ::=(2;2;0) x::node<val1,next1>@M * H(next1,v)&v!=val1
   \/ (1;2;0) x::node<val,next>@M * DP_1017(next,v)&v=val \/ (1;0) emp&x=null,
 G(x,v,res) ::=(2;2;0) x::node<val,next>@M * G(next,v,res)
   \/ (1;2;0) x::node<v,next>@M * DP_1017(next,v)&res & v=val
   \/ (1;0) emp&!res & x=null,
 DP_1017(next,v) ::=(1;2;0) NONE]

case spec

From base case of post
\/ (1;2;0) x::node<v,next>@M * DP_1017(next,v)&res & v=val
   \/ (1;0) emp&!res & x=null

res is disjoint and input also disjoint --> split it
partial split: 
 or
 fully spit: trace is disjoint
*/
