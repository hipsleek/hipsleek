

data node {
	int val;
	node next;
}

ll<n> == self=null & n=0
	or self::node<_, q> * q::ll<n-1>
	inv n>=0;

/* single conditional
 is disjunct in Octx or [OCtx]? */



node f(int x)
requires true
ensures res::ll<1> & 4<x
    or res::ll<2> & 0<x<=4
    or res::ll<3> & x<=0;
{
 node y;
 if (x>0) {
       y=new node(1,null);
 } else {
      y=new node(5,new node(6,null));
};
dprint;
 if (x>4) {
       y=y;
//       dprint;
} else{
   y=new node(2,y);
//   dprint;
};
dprint;
 return y;
}


