data node1 { 
  int val; 
  node1 next; 
}

ll<n> == self=null & n=0 
  or self::node1<_,p> * p::ll<m> & n=m+1 
  inv n>=0;

sll<n,xs,xl> == self::node1<xs,null> & n=1 & xs=xl 
  or self::node1<xs,p> * p::sll<m,k,xl> & n=m+1 & xs<=k 
  inv xs<=xl & n>=1;


relation A(int a, int b, int c, int d, int e).

void sort_insert_sll(node1 x, int v)
  infer [A,v,xs]
  requires x::sll<n,xs,xl> /* & v>=xs*/
  ensures x::sll<m,mn,mx>  & m=n+1  & A(mn,mx,v,xs,xl) /* & mn=min(v,xs) & mx=max(v,xl)*/ ;
{
  node1 w;
  w = x.next;
  if (w == null)
    x.next = new node1(v, null);
  else {
    if (v < w.val)
      x.next = new node1(v, w);
    else sort_insert_sll(w, v);
  }
}
