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

ll2<n,V,B> == self=null & n=0 & B={} & V={}
   or self::node<t, _,_,_,k> * t::ll2<n-1,V1,B1> & B=union({self},B1)
  & V=union({k},V1)
	inv n>=0;

ll3<n,V,B> == self::node<null,_,_,_,k> & V={k} & B={self} & n=1
   or self::node<t, _,_,_,k> * t::ll3<n-1,V1,B1> & B=union({self},B1)
  & V=union({k},V1)
  inv n>=0 & self!=null & V!={} & B!={};

// free variable error
/* ll2<n,V,B> == self=null & n=0 & B={} & v={} */
/*    or self::node<t, _,_,_,k> * t::ll2<n-1,V1,B1> & B=union({self},B1) */
/*   & V=union({k},V1) */
/* 	inv n>=0; */

// mona translation bug!

void append(node x, node y)

  // OK
  /* requires x::ll<a,S1> * y::ll<b,S2> & x != null */
  /* ensures x::ll<a+b,S> & S = union(S1, S2); */

  // OK
  /* requires x::ll3<_,V1,S1> * y::ll3<_,V2,S2>  */
  /* ensures x::ll3<_,V,S> & S = union(S1, S2) & V=union(V1,V2); */

  // OK
  /* requires x::ll3<a,_,_> * y::ll3<b,_,_>  */
  /* ensures x::ll3<a+b,_,_> ; */

  // OK with -tp mona -tp om 
  requires x::ll3<a,V1,S1> * y::ll3<b,V2,S2>
  ensures x::ll3<a+b,V,S> & S = union(S1, S2) & V=union(V1,V2);

  // OK
  /* requires x::ll2<a,V1,S1> * y::ll2<b,V2,S2> & x != null */
  /* ensures x::ll2<a+b,V,S> & S = union(S1, S2) & V=union(V1,V2); */

  /* wrong pre */
  /* requires x::ll<a,S1> * y::ll<b,S2> // & x != null */
  /* ensures x::ll<a+b,S> & S = union(S1, S2); */

  /* wrong post */
  /* requires x::ll<a,S1> * y::ll<b,S2> & x != null */
  /* ensures x::ll<a+b+1,S> & S = union(S1, S2); */

{
	if (x.next==null)
    {      
      x.next = y;
      //dprint;
      //assume false;
    }
	else
   {
    //assume false;
		append(x.next, y);
    }
}
