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

bool foo(node x, node y)
/*
  requires x::ll<n> * y::ll<m>
  ensures n=m & res or n!=m & !res;
*/
/*
// Total verification time: 0.54 second(s)
        Time spent in main process: 0.3 second(s)
        Time spent in child processes: 0.24 second(s)
*/
  requires x::ll<n> * y::ll<m> & n=m
  ensures res;
  requires x::ll<n> * y::ll<m> & n!=m
  ensures !res;
/*
Total verification time: 0.69 second(s)
        Time spent in main process: 0.36 second(s)
        Time spent in child processes: 0.33 second(s)
*/

/*
  requires x::ll<n> * y::ll<m>
   case {
     n=m -> ensures res;
     n!=m -> ensures !res;
   }
*/
/*
        Time spent in main process: 0.35 second(s)
        Time spent in child processes: 0.3 second(s)
    Total verification time: 0.65 second(s)
*/
/*
  requires x::ll<n> * y::ll<m>
   case {
     n=m -> ensures res;
    n>m -> ensures !res;
    n<m -> ensures !res;
   }
*/
/*
// Total verification time: 0.86 second(s)
        Time spent in main process: 0.45 second(s)
        Time spent in child processes: 0.41 second(s)
*/

{ if (x==null)
    if (y==null) return true;
    else return false;
  else if (y==null) return false;
    else return foo(x.next,y.next);
} 


/*
void loop(node x)
/*
  requires x::ll<n> & n>1
  ensures x::ll<n-1>;
  requires x::llast<n,v> & n>1
  ensures x::llast<n-1,v>;
*/

  requires [v] x::lseg<v,p>*p::node<w,null> 
  ensures x::lseg<w,null>;


{
  if (x.next.next==null) {
    x.val = x.next.val;
    x.next= null;
  } else {
    //assume false;
    node tmp=x.next;
    dprint;
      assert tmp'::lseg<a,r>*r::node<b,null> & a=v & b=w;
      loop(tmp);
      dprint;
      //assume false;
  }
}

*/

/*

  requires [glob] (x::ll<n> & glob=1 or x::ss<n> & glob=2)
  ensures  res=2 & glob=1 or res=3 & glob=2

  requires [glob] (x=null & glob=1 | x!=null glob=2)
  ensures  res=2 & glob=1 or res=3 & glob=2

  requires [glob] (x::ll<n>  & glob=1)
        or [glob] (x::ss<n> & glob=2)
  ensures  res=2 & glob=1 or res=3 & glob=2

 requires (x::ll<n>  & glob=1)
        or (x::ss<n> & glob=2)
  ensures  res=2 & glob=1 or res=3 & glob=2
*/
