data node {
  node next; 
  node p;
  node l;
  node r;
  int key;
}

ll6<n,B> == self=null & n=0 & B={0}
	or self::node<t, _,_,_,k> * t::ll6<n-1,B1> & B=union({self},B1)
	inv n>=0;

// mona translation bug!


