/* singly linked lists */

/* representation of a node */
data node {
	int val;
	node next;
}

/* view for a singly linked list */
ll<n> == self = null & n = 0
	or self::node<_, q> * q::ll<n-1>
  inv n >= 0;

HeapPred H(node a).
//HeapPred G(node a, node b).
HeapPred H1(node a).
void dispose(ref node x)
  requires x::node<_,_>
  ensures x'=null;


//The number of elements that conform the list's content.
//relation SIZEH(int a, int b, int c).
int size_helper(node x, ref int n)
  infer[H,H1]
  requires H(x) //0<=m
     ensures  H1(x);// & SIZEH(res,n);//res=m+n & m>=0
{
  if (x==null) 
    return n;
  else {
    n = n+1;
    return size_helper(x.next, n);
  }
}


/*
 H(x)&x=null --> H1(x)
 H(x)&x!=null --> x::node<val_81_1002',b> * HP_2155(b,x)
 HP_2155(b,x) * x::node<_,b>&x!=null--> H(b)
 x::node<_,_>&x!=null --> H1(x)

normalize:
Drop 2nd paramiter of HP_2155
 H(x)&x=null --> H1(x)
 H(x)&x!=null --> x::node<val_81_1002',b> * HP_2155(b)
 HP_2155(b) * x::node<_,b>&x!=null--> H(b)
 x::node<_,_>&x!=null --> H1(x)  (************************)

H(x) -> x = null
H(x) &x!=null -> x::node<_,b> * H(b)
 H(x)&x=null --> H1(x)
x::node<_,_> --> H1(x)


DEBUG:
### action =  InferHeap: ( H1(x), emp)
 ### estate =  x'::node<val_64_1082,v_node_64_1087>@M[Orig] * H1(v_node_64_1087)&x'=x & x'!=null & !(v_bool_60_1006') & x'!=null & !(v_bool_60_1006') & SIZEH(v_int_64_1005',1+n) & res=v_int_64_1005'&{FLOW,(22,23)=__norm}[]
  es_infer_vars_rel: [SIZEH]
  es_var_measures: MayLoop
 ### conseq =  H1(x)&true&{FLOW,(22,23)=__norm}[]


(RELASS [H1], x::node<val_64_1082,v_node_64_1087>@M[Orig]&x!=null&{FLOW,(22,23)=__norm}[], H1(x)&true&{FLOW,(22,23)=__norm}[])]


*/
