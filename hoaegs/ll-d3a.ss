data node {
	int val;
	node next
}

relation dm(int[] a, int low, int high).

axiom dm(a,low,high) & low<=l & h<=high ==> dm(a,l,h).
//axiom dm(a,l+1,h) & dm(a,l,l+1)  ==> dm(a,l,h).
//axiom dm(a,l,h-1) & dm(a,h-1,h) ==> dm(a,l,h).
axiom l>=h ==> dm(a,l,h).
axiom dm(a,l,k) & dm(a,k,h) ==> dm(a,l,h).

ll2<i,j,aaa> == self = null & i=j //& dm(aaa,i,j)
  or self::node<v, r> * r::ll2<i+1,j,aaa> & aaa[i]=v
      & dm(aaa,i,i+1) 
     inv i<=j & dm(aaa,i,j);

void foo(node x)
 requires x::ll2<i,j,aaa>
 ensures x::ll2<i,j,bbb> & forall(k:!(i<=k<j)|bbb[k]=aaa[k]+1) ;
{
  if (x==null) { 
    return;
  } else {
    //assume false;
    int t = x.val+1;
    x.val = t;
    //assume bbb[i]=t' & dm(bbb,i,i+1); //'
    foo(x.next);
    dprint;
    //return x;
  }
}

/*
void foo$node(  node x) rec
static  :EBase exists (Expl)[](Impl)[i; j; aaa](ex)[]x::ll2<i,j,aaa>@M&
        {FLOW,(24,25)=__norm}[]
          EBase emp&MayLoop[]&{FLOW,(1,27)=__flow}[]
                  EAssume 
                    (exists i_42,j_43,bbb: x::ll2<i_42,j_43,bbb>@M&
                    forall(k:(!((i<=k & k<j)) | bbb[k]=1+(aaa[k]))) & 
                    i=i_42 & j=j_43&{FLOW,(24,25)=__norm})[]


 */
