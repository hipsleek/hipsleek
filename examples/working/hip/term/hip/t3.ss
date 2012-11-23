
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
 x>0 -> ensures  "post1": res::ll<1>;
 x<=0 -> ensures "post2": res::ll<2>;
 }

{
 node y;
 if (x>0) {
    y=new node(1,null);
  // dprint;
   assert "post1": true ;
   assert "post2": false ;
  //assert false;
  } else { 
    y=new node(5,new node(6,null));
    // assert "post1": false ;
     //assert "post2": y'::ll<2> ;
  }
//assert true ;
//assert true assume false;
//g();
//assert false assume true;
//dprint;
//assert false;
return y;
}

//node g() 
//requires false
//ensures true;
