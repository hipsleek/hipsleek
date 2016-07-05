
data node {
	int val; 
	node next; 
}

sortHO<v,R:relation(int,int)> == 
  self::node<v,null> 
  or self::node<v, p> * p::sortHO<v2,R> & R(v,v2) 
inv self!=null;

relation R0(int r, int a).
relation R1(int r, int a).
relation R2(int r, int a).

relation R(int r, int a) == r<=a .
relation LT(int r, int a) == r>a .

node id(node x)
  infer [R1,R2]
  requires x::sortHO<a,R1>
  ensures  res::sortHO<a,R2> & res=x;
/*
  # R1(a,b)-->R2(a,b)

  RELDEFN R2: ( a=a_30 & v2_590=v2_622 & R1(a,v2_590)) -->  R2(a_30,v2_622)]

*/
{
    node tmp = x.next;
    if (tmp==null) return x;
    else {
      tmp=id(tmp);
      return x;
    }
}

