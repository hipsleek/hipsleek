data node {
 int val;
 node next;
}

HeapPred H(node x, int v). // non-ptrs are @NI by default
PostPred G(node x, int v). // non-ptrs are @NI by default
sortll<n> == self=null
 or self::node<v,q>*q::sortll<v> & n<=v
 inv true; 

bool check_sorted(node x, int v)
infer [H,G] requires H(x,v) ensures G(x,v) & res;
//requires x::sortll<v>@L ensures  res;
{ 
  if (x==null) return true;
  else {int t=x.val; return (v<=t &&  check_sorted(x.next,t));};
} 

/*
# check-sorted-2.ss --sa-en-pure-field 

PROBLEM : this guarded form is unnecessary.

 HP_930(next_17_928,v@NI)&
  v<=val_17_927 |#| x::node<val_17_927,next_17_928>@M --> H(next_17_928,val_17_927@NI).

*/
