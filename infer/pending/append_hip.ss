data node1 { 
  int val; 
  node1 next; 
}

lseg<p,A> == self=p & A=0 
  or self::node1<_,q> * q::lseg<p,B> & B=A;

ll<n> == self=null & n=0 
  or self::node1<_,p> * p::ll<m> & n=m+1 
  inv n>=0;

sll<n,mn,mx> == self::node1<mn,null> & mn=mx & n=1 
  or self::node1<mn,p> * p::sll<m,k,mx> & n=m+1 & mn<=k 
  inv mn<=mx & n>=1;

/*
void append_ll(node1 x, node1 y)
  requires x::ll<xn> * y::ll<yn>
  ensures x::ll<m>;
{
  node1 w;
  w = x.next;
  if (w == null) x.next = y;
  else append_ll(w, y);
}
*/

relation M(int x, int y).
relation N(int x, int y, int z).
relation R(int x, int y).

void append_sll(node1 x, node1 y)
  infer [M]
  requires x::sll<xn,xs,xl> * y::sll<yn,ys,yl> & xl<=ys // & M(xl,ys)
  ensures x::sll<m,rs,rl> & rl=yl & m>=1+yn & N(m,xn,yn);
{
  node1 w;
  w = x.next;
  if (w == null) {
    x.next = y;
    dprint;
  }
  else{
    assume false;
    append_sll(w, y);
  }
}

