data node {
  int val;
  node next;
}

HeapPred P(int k, node x).
HeapPred Q(int k, node x).

ll<n> == self=null & n = 0
  or self::node<_, r> * r::ll<n2> & n = 1 + n2;

node fcode(int k, node x)
  requires P(k, x)
  ensures Q(k, x);

int length(node x)
  requires x::ll<n>
  ensures x::ll<n> & res = n;
{
  if (x == null) return 0;
  else {
    int k;
    // x::ll<n> & x != null
    fcode(k, x);
    // ll(x,n) & n = res -> ll(x, n) & n = k
    // Q(k, x) & x != null
    return k;
  }
}
// ( x::ll<n>@M&!(v_bool_20_1893') & x'=x & x'!=null&{FLOW,(4,5)=__norm#E}[],
// P(k',x') * T0(n,x,x')&{FLOW,(4,5)=__norm#E}[]),

// ( T0(n,x,x') * Q(res,x')&{FLOW,(4,5)=__norm#E}[],
// (exists n_94: x::ll<n_94>@M&res=n & n_94=n 

// Q(res,x) & !(v_bool_20_1893) & x!=null & |- (exists n_94: x::ll<n_94>@M&res=n
// & n_94=n)
 
// k = 1 + length(x.next)
// unfold-pre -> unfold-post
