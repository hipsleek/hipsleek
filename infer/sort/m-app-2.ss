
data node {
	int val; 
	node next; 
}

sortHO<v,mi,mx> == 
  self::node<mi,null> & mi=mx & v=mi
  or self::node<v, p> * p::sortHO<v2,mi2,mx2> & mi=min(v,mi2) & mx=max(v,mx2) 
inv self!=null;


node append(node x, node y)
  //infer [R1,R2]
  requires x::sortHO<a,mi,mx> * y::node<b,null>
  ensures  res::sortHO<a,mi2,mx2>  & x=res
  & mi2=min(mi,b) & mx2=max(mx,b)
  ;
/*
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

