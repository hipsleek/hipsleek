/* selection sort */

data node {
	int val; 
	node next; 
}


llMM<mi> == self::node<v,null> & mi=v  
  or self::node<v, p> * p::llMM<mi2> & mi=min(v,mi2) 
  //& v<=mi2
inv self!=null;

relation P3(int a1, int a2,int a3).
relation P4(int a1, int a2,int a3).
relation P5(int a1, int a2,int a3).
relation P6(int a1, int a2,int a3).

node sel(ref node x)
     requires x::llMM<mi> 
     ensures  res::node<mi,_> & x'=null
           or res::node<mi,_> * x'::llMM<mi2> & mi<=mi2
     ;
/*


*/
{
  node tmp;
  dprint;
  tmp =x.next;
  dprint;
  if (tmp==null)
    { dprint;
      tmp=x; x=null; return tmp;}
  else {
    dprint;
    node n = sel(tmp);
    dprint;
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

