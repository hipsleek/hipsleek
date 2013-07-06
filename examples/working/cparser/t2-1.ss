data node {
  int val;
  node__star next;
}

data node__star {
  node pdata;
}

ll<n> == self=null & n=0
  or self::node__star<p> * p::node<_, q> * q::ll<n-1>
  inv n>=0;

node__star f(int x)
  requires true
  ensures res::ll<1> & 4<x
      or res::ll<2> & 0<x<=4
      or res::ll<3> & x<=0;
{
  node__star y;
  if (x>0) {
    y = new node__star(new node(1, null));
  } else {
    y = new node__star(new node(5, new node__star(new node(6, null))));
  }
 
  if (x>4) {
    y=y;
  } else{
    y = new node__star(new node(2, y));
  };
  
  return y;
}


