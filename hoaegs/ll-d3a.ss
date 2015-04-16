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
 // mark this bbb as instantiable ghost 
{
  if (x==null) { 
    return;
  } else {
    //assume false;
    int t = x.val+1;
    x.val = t;
    assume bbb[i]=t' & dm(bbb,i,i+1); //'
    foo(x.next);
    dprint;
    //return x;
    dprint;	
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

[
 Label: [(,1 ); (,2 )]
 State:
(exists bbb_1050: x'::node<t_46',r_1027>@M * 
  r_1027::ll2<i_1043,j_1044,bbb_1050>@M&flted_15_1025=1+i & v_1026=aaa[i] & dm(aaa,i,1+i) & j=j_1023 & aaa=aaa_1024 & x=x' & x'!=null & !(v_bool_23_975') & x'!=null & !(v_bool_23_975') & t_46'=1+v_1026 & v_1026=val_28_1038 & flted_15_1025=i_1043 & j_1023=j_1044 & aaa_1024=aaa_1045 & flted_15_1025<=j_1023 & dm(aaa_1024,flted_15_1025,j_1023) 
& forall(k:(!((i_1043<=k & k<j_1044)) | bbb_1050[k]=1+(aaa_1045[k]))) 
& i_1043<=j_1044 & dm(aaa_1045,i_1043,j_1044)&{FLOW,(24,25)=__norm})[]
       es_heap: emp
       es_var_measures 2: MayLoop[]
       es_cond_path: [2; 0]

 ]


dm(aaa,1+i,j_1044) & (1+i)<=j_1044 & dm(aaa,i,1+i) & (((i_1043<j_1044 & 
r_1027!=null) | (r_1027=null & i_1043=j_1044))) & v_1073=1+(aaa[i]) & 
dm(aaa,i_1043,j_1044) & i_1043<=j_1044 
& forall(k:(!((i_1043<=k & k<j_1044)) | bbb_1068[k]=1+(aaa[k]))) 
& i_1043=1+i 
|-  exists(bbb_1072:bbb_1068=bbb_1072 & exists(i_1070:i_1043=i_1070+1 & 
v_1073=bbb_1072[i_1070] & dm(bbb_1072,i_1070,i_1070+1))). LOCS:[28;27;16;1;15;17;21;30;0] (may-bug)



 */
