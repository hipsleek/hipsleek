data node {
  node next; 
  node p;
  node l;
  node r;
  int key;
}

sll<n,sm,lg> == self::node<t,_,_,_,_> & sm<=lg & n=0
  //  or self::node<t, _,_,_,sm> * t::sll<n-1,sm1,lg> & sm<=sm1 
	inv n>=0 & sm<=lg;

sll2<n,sm,lg> == self=null & sm<=lg & n=0
    or self::node<t, _,_,_,sm> * t::sll2<n-1,sm1,lg> & sm<=sm1 
	inv n>=0 & sm<=lg;

sll3<n,sm,lg> == self=null & sm<=lg & n=0
    or self::node<t, _,_,_,_> * t::sll3<n-1,sm1,lg> & sm<=sm1 
	inv n>=0 & sm<=lg;

sll4<n,sm,lg> == self=null & sm<=lg & n=0 & 0.0<=sm
    or self::node<t, _,_,_,_> * t::sll4<n-1,sm1,lg> & sm<=sm1 
	inv n>=0 & sm<=lg;

/* sll5<n,sm,lg> == self=null & sm<=lg & n=0 & 0.0<=sm */
/*     or self::node<t, _,_,_,sm> * t::sll5<n-1,sm1,lg> & sm<=sm1  */
/* 	inv n>=0 & sm<=lg; */


// mona translation bug!


