//Use array instantiation with z3 ./hip wand/arraymark.ss -tp z3 --allow-array-inst

data node {
	int val;
	node next
}

relation dm(int[] a, int low, int high).

axiom dm(a,low,high) & low<=l & h<=high ==> dm(a,l,h).
axiom l>=h ==> dm(a,l,h).
axiom dm(a,l,k) & dm(a,k,h) ==> dm(a,l,h).

ll2<i,j,aaa> == self = null & i=j 
  or self::node<v, r> * r::ll2<i+1,j,aaa> & aaa[i]=v
      & dm(aaa,i,i+1) 
     inv i<=j & dm(aaa,i,j);

void foo(node x)
 requires x::ll2<i,j,aaa>
 ensures x::ll2<i,j,bbb> & forall(k:!(i<=k<j)|bbb[k]=aaa[k]+1) ;
 // mark this bbb as instantiable ghost 
{
  if (x==null) { 
    return;
  } else {
    int t = x.val+1;
    x.val = t;
    assume bbb[i]=t' & dm(bbb,i,i+1); //'
    foo(x.next);
  }
}
