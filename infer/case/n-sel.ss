/* selection sort */

data node {
	int val; 
	node next; 
}


llMM<mi> == self::node<v,null> & mi=v  
  or self::node<v, p> * p::llMM<mi2> & mi=min(v,mi2) 
  //& v<=mi2
inv self!=null;

node sel(ref node x)
     requires x::llMM<mi> 
     ensures  res::node<mi,_> & x'=null
           or res::node<mi,_> * x'::llMM<mi2> & mi<=mi2
     ;
/*


*/
{
  node tmp;
  if (x.next==null)
    { tmp=x; x=null; return tmp;}
  else {
    tmp = x.next;
    node n = sel(tmp);
    if (n.val<=x.val) {
       x.next = tmp;
       return n;
    } else {
      node r = x;
      n.next = tmp;
      x = n;
      return r;
    }
  }
}

