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

ll2<n,B> == self=null & n=0 & B={}
	or self::node<t, _,_,_,k> * t::ll2<n-1,B1> & B=union({k},B1)
	inv n>=0;

ll3<n,B> == self=null & n=0 & B={}
  or self::node<t, _,_,_,k> * t::ll3<n-1,B1> & B=union({null},B1)
	inv n>=0;

ll4<n,B> == self=null & n=0 & B={}
	or self::node<t, _,_,_,k> * t::ll4<n-1,B1> & B=union({},B1)
	inv n>=0;

ll5<n,B> == self=null & n=0 & B={0}
	or self::node<t, _,_,_,k> * t::ll5<n-1,B1> & B=union({2},B1)
	inv n>=0;

ll6<n,B> == self=null & n=0 & B={0}
	or self::node<t, _,_,_,k> * t::ll6<n-1,B1> & B=union({self},B1)
	inv n>=0;

// mona translation bug!


