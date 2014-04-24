
data node {
	int val; 
	node next; 
}

sortHO<v,R:relation(int,int),mi,mx> == 
  self::node<mi,null> & mi=mx & v=mi
  or self::node<v, p> * p::sortHO<v2,R,mi2,mx2> & R(v,v2) & mi=min(v,mi2) & mx=max(v,mx2) 
inv self!=null;

relation R0(int r, int a, int c).
relation P2(int r, int a).
relation R1(int r, int a).
relation R2(int r, int a).

relation R(int r, int a) == r<=a .
relation LT(int r, int a) == r>a .

node append(node x, node y)
  infer [R0,R1,P2]
  requires x::sortHO<a,R1,mi,mx> * y::node<b,null> &  P2(mx,b)
  ensures  res::sortHO<a,R2,mi2,mx2> & mi2=min(mi,b) & mx2=max(mx,b) & res=x;
/*
  # R1(a,b)-->R2(a,b)

  RELDEFN R2: ( a=a_30 & v2_590=v2_622 & R1(a,v2_590)) -->  R2(a_30,v2_622)]

*/
{
    node tmp = x.next;
    if (tmp==null) {
        x.next=y;
        return x;
    } else {
      tmp=append(tmp,y);
      return x;
    }
}

