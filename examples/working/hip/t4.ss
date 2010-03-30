
data node {
	int val;
	node next;
}

ll<n> == self=null & n=0
	or self::node<_, q> * q::ll<n-1>
	inv n>=0;

// selective assert testing
// is the selective assert testing working?

node f(int x)
/*
requires true
ensures res::ll<1> & x>0
    or res::ll<2> & x<=0; 
*/
 case {
 x>0 -> ensures  "post1": res::ll<1 >;
 x<=0 -> ensures "post2": res::ll<2>;
 }
{
 node y;
 if (x>0) {
    //y.val =0;  // failing here..
    y=new node(1,null);
  } else { 
    //y.val =0;  // failing here..
    y=new node(5,new node(6,null));
  }
//dprint;
//y=null;
dprint;
return y;
//dprint; // why isnt flow changed to return ?
//assert true;
}

