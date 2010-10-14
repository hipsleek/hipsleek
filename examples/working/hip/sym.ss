data node {
	int val;
	node next;
}

ll<n> == self=null & n=0
	or self::node<_, q> * q::ll<n-1>
	inv n>=0;

llast<n,v> == self::node<v,null> & n=1
  or self::node<_, q> * q::llast<n-1,v>
	inv n>=1;

lseg<v,p> == self::node<v,p> 
  or self::node<w, q> * q::lseg<v,p> 
   inv self!=null;
    /*

requires x::lseg<S,v,p>*p::node<w,null>
 ensures x::lseg<S,w,null>

  requires x::lseg<L,p>*p::node<w,q>*q::node<v,null>
  ensures x::lseg<L,p>*p::node<v,null>

  requires x::lseg<v,p>*p::node<w,null>
  ensures x::lseg<w,p>;

*/

void loop(node x)
/*
  requires x::ll<n> & n>1
  ensures x::ll<n-1>;
  requires x::llast<n,v> & n>1
  ensures x::llast<n-1,v>;
*/

  requires x::lseg<v,p>*p::node<w,null>
  ensures x::lseg<w,null>;


{
  if (x.next.next==null) {
    x.val = x.next.val;
    x.next= null;
  } else {
    //assume false;
    node tmp=x.next;
    dprint;
      assert tmp'::lseg<v,p>*p::node<w,null>;
      loop(tmp);
      dprint;
      assume false;
  }
}

