data node {
  node next; 
  node p;
  node l;
  node r;
  int key;
}

ll<n,B> == self=null & n=0 & B={}
	or self::node<t, _,_,_,k> * t::ll<n-1,B1> & B=union({self},B1)
	inv n>=0;

// mona translation bug!

