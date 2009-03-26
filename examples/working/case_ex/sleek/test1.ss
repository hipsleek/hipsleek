
data node { int val ; node next }.

data node2 { int val ; node2 l; node2 r; }.

data node4 { int val ; int ht;node4 l; node4 r; }.
		
pred tree<h,bal> == case { 
			self=null  -> [] h=0 & bal=1 ;          
			self!=null -> [] self::node4<_,h,lt,rt>* lt::tree<h1,_>* rt::tree<h2,_> & h=1+max(h1,h2) 
              case { h1<h2 -> [] bal=0 ;
                     h1=h2 -> [] bal=1 ;
                     h1>h2 -> [] bal=2 ;
				   };
			} inv h>=0&bal>=0&bal<=2.

checkentail x=null |- x::tree<h,bal> .	
print residue.
checkentail x=null |- x::tree<h,bal> & bal=1 & h=0.
print residue.


checkentail x::node4<_,h,lt,rt>*lt::tree<h1,_> * rt::tree<h2,_> & h1=h2 &h = 1+max(h1,h2)|- x::tree<h,bal>.
print residue.


checkentail x::node4<_,h,lt,rt>*lt::tree<h1,_> * rt::tree<h2,_> &h1=h2&h=1+h1 |- x::tree<h,bal> & bal=1.
print residue.


checkentail x::node4<_,h,lt,rt>*lt::tree<h1,_> * rt::tree<h2,_> &h1>h2&h=1+h1 |- x::tree<h,bal> & bal=1.
print residue.

pred ll<n> == case {
         self=null -> [] n=0;
         self!=null -> [] self::node<tz,q>*q::ll<n-1>;} inv n>=0.


checkentail x::ll<m> |- 
		case { 
			x=null  -> 
					[] x=null; 
			x!=null -> 
					[] x::node<_,q>;
			}.
print residue.

checkentail x::ll<m> |-  x=null or x::node<_,q>.
print residue.


/*
	
pred avl<h,bal> == case { 
			self=null -> [] self=null & bal=1 &h=0;
            self!=null -> [] self::node4<_,h,lt,rt>*lt::avl<h1,_>*rt::avl<h2,_> & h=1+max(h1,h2)& bal=h1-h2+1 & -1<=h1-h2<=1;}
		inv h>=0 & 0<=bal<=2.

pred tree1<h,bal> == case { 
			self=null  -> [] h=0 & bal=1 ;          
			self!=null -> [] self::node4<_,h,lt,rt>* lt::tree1<h1,_>* rt::tree1<h2,_> & h=1+max(h1,h2) &
				(
				h1<h2 &
				bal=0
				
				|
				h1=h2 & bal=1|
				h1>h2 & bal=2);
			}.

	 
pred ll1<n> == case {
         n=0 -> [] self=null ;
         n>0 -> [] self::node<_,q>*q::ll1<n-1> ;
		 n<0 -> [] false;}
        inv n>=0.
*/