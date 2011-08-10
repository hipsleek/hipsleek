/*data cl {int val;}.
data cl2 {int val;}.
data cl3 {int val;}.

checkentail x::cl<n> & n > 3 |- x::cl<m> & m > 2.
//valid
checkentail x::cl<n> & n > 1 |- x::cl<m> & m > 2.
//fail
checkentail x::cl<_> |- x::cl<_>.
//valid
checkentail x::cl@[L,R]<_> |- x::cl<_>.
//fail
checkentail x::cl@[L,R]<_> |- x::cl@[L]<_>.
//fail
checkentail x::cl@[L]<_> |- x::cl@[R]<_>.
//fail
checkentail x::cl<_> |- x::cl@[R]<_>.
print residue.
//valid
checkentail x::cl<_> |- x::cl@[L]<_>.
print residue.
//valid

checkentail x::cl@[L,R]<_> |- x::cl<_>.
//fail
checkentail x::cl@[R,R]<_> |- x::cl[L,R]<_>.
//fail
checkentail x::cl@v<_> |- x::cl@v<_>.
//valid

checkentail x::cl@v1<_> |- x::cl@v<_>. 
//valid

checkentail x::cl@[R]<_> |- x::cl@[R,L]<_>.
print residue.
//valid

checkentail x::cl@[L]<_> * x::cl@[R]<_>|- x::cl<_>.
//valid

checkentail x::cl@[L]<_> * x::cl@[R]<_>|- x::cl@v<_>.
print residue.
//valid

checkentail x::cl@[L]<_> * x::cl@[R]<_>|- x::cl@v<_> & join([L],[R,L],v).
print residue.
//valid

checkentail x::cl@[L]<_> * x::cl@[R]<_>|- x::cl@v<_> & join ([L],[R,L],v).
//valid

checkentail x::cl@[L]<_> * x::cl@[R]<_>|- x::cl@v<_> & join ([R],[R,L],v).
//fail

checkentail x::cl@v<_> &join ([L],[L,R],v)|- x::cl@v<_> & join ([R],[R,L],v).
//valid

checkentail x::cl@[L]<_> * x::cl@[R]<_>|- 1>2.
//fail

checkentail x::cl@[L]<_> * x::cl@[L,R]<_>|- 1>2.
//valid 
 
barrier b1n, 2, [(0,1,[
 requires x1::cl@[L]<A>*x2::cl@[L]<B>*y1::cl@[L]<C>*y2::cl@[L]<D>*i::cl@[L]<T>*self::b1n@[L]<0> ensures x1::cl@[L]<A>*x2::cl@[L]<B>*y1::cl<C>*i::cl@[L]<T>*self::b1n@[L]<1>;,
 requires x1::cl@[R]<A>*x2::cl@[R]<B>*y1::cl@[R]<C>*y2::cl@[R]<D>*i::cl@[R]<T>*self::b1n@[R]<0> ensures x1::cl@[R]<A>*x2::cl@[R]<B>*y2::cl<D>*i::cl@[R]<T>*self::b1n@[R]<1>;]),	
 (1,2,[
 requires x1::cl@[L]<A>*x2::cl@[L]<B>*y1::cl<C>*i::cl@[L]<T>*self::b1n@[L]<1>&T<30 ensures x1::cl<A>*y1::cl@[L]<C>*y2::cl@[L]<D>*i::cl<T>*self::b1n@[L]<2>&T<30;,
 requires x1::cl@[R]<A>*x2::cl@[R]<B>*y2::cl<D>*i::cl@[R]<T>*self::b1n@[R]<1>&T<30 ensures x2::cl<B>*y1::cl@[R]<C>*y2::cl@[R]<D>*         self::b1n@[R]<2>;]),
 (2,1,[
 requires x2::cl<B>*y1::cl@[R]<C>*y2::cl@[R]<D>*         self::b1n@[R]<2> ensures x1::cl@[R]<A>*x2::cl@[R]<B>*y2::cl<D>*i::cl@[L]<T>*self::b1n@[R]<1>;,
 requires x1::cl<A>*y1::cl@[L]<C>*y2::cl@[L]<D>*i::cl<T>*self::b1n@[L]<2> ensures x1::cl@[L]<A>*x2::cl@[L]<B>*y1::cl<C>*i::cl@[R]<T>*self::b1n@[L]<1>;]) ,
 (1,3,[
 requires x1::cl@[L]<A>*x2::cl@[L]<B>*i::cl@[L]<T>*self::b1n@[L]<1>& T>=30 ensures x1::cl@[L]<A>*x2::cl@[L]<B>*i::cl<T>*self::b1n@[L]<3> & T>=30;, 
 requires x1::cl@[R]<A>*x2::cl@[R]<B>*i::cl@[R]<T>*self::b1n@[R]<1>& T>=30 ensures x1::cl@[R]<A>*x2::cl@[R]<B>         *self::b1n@[R]<3>;])].
 
  
barrier b2n, 2, [(0,1,[
 requires x1::cl@[L]<A>*x2::cl@[L]<B>*y1::cl@[L]<C>*y2::cl@[L]<D>*i::cl@[L]<T>*self::b2n@[L]<0> ensures x1::cl@[L]<A>*x2::cl@[L]<B>*y1::cl<C>*i::cl@[L]<T>*self::b2n@[L]<1>;,
 requires x1::cl@[R]<A>*x2::cl@[R]<B>*y1::cl@[R]<C>*y2::cl@[R]<D>*i::cl@[R]<T>*self::b2n@[R]<0> ensures x1::cl@[R]<A>*x2::cl@[R]<B>*y2::cl<D>*i::cl@[R]<T>*self::b2n@[R]<1>;]),	
 (1,2,[
 requires x1::cl@[L]<A>*x2::cl@[L]<B>*y1::cl<C>*i::cl@[L]<T>*self::b2n@[L]<1>&T<30 ensures x1::cl<A>*y1::cl@[L]<C>*y2::cl@[L]<D>*i::cl<T>*self::b2n@[L]<2>&T<30;,
 requires x1::cl@[R]<A>*x2::cl@[R]<B>*y2::cl<D>*i::cl@[R]<T>*self::b2n@[R]<1>&T<30 ensures x2::cl<B>*y1::cl@[L]<C>*y2::cl@[R]<D>*         self::b2n@[R]<2>;]),
 (2,1,[
 requires x2::cl<B>*y1::cl@[R]<C>*y2::cl@[R]<D>*         self::b2n@[R]<2> ensures x1::cl@[R]<A>*x2::cl@[R]<B>*y2::cl<D>*i::cl@[L]<T>*self::b2n@[R]<1>;,
 requires x1::cl<A>*y1::cl@[L]<C>*y2::cl@[L]<D>*i::cl<T>*self::b2n@[L]<2> ensures x1::cl@[L]<A>*x2::cl@[L]<B>*y1::cl<C>*i::cl@[R]<T>*self::b2n@[L]<1>;]) ,
 (1,3,[
 requires x1::cl@[L]<A>*x2::cl@[L]<B>*i::cl@[L]<T>*self::b2n@[L]<1>& T>=30 ensures x1::cl@[L]<A>*x2::cl@[L]<B>*i::cl<T>*self::b2n@[L]<3> & T>=30;, 
 requires x1::cl@[R]<A>*x2::cl@[R]<B>*i::cl@[R]<T>*self::b2n@[R]<1>& T>=30 ensures x1::cl@[R]<A>*x2::cl@[R]<B>         *self::b2n@[R]<3>;])].
 */

 data node { int val ; node next }.

pred ll<n> == self = null & n = 0
	or self::node<next = r> * r::ll<n - 1>
	inv n >= 0.
/*
 checkentail x::ll<n> |- x::node<_,_>.
 //fail
 
 checkentail x::ll<n> |- x::ll<m>.
 //valid
 
 checkentail x::ll@v<n> |- x::ll@v<m>.
 //valid
 
 checkentail x::ll@[R]<n> |- x::ll@[R,R]<m>.
 print residue.
 //valid
 
  checkentail x::ll@[R]<n> & n>0 |- x::node<_,_>.
 //fail
 
 checkentail x::ll@[R]<n> & n>0 |- x::node@[R]<_,_>.
 print residue.
 //valid
 
 checkentail x::ll@[R]<n> & n>0 |- x::node@[R,R]<_,_>.
 print residue.
 //valid
 
 checkentail x::ll@[R]<n> & n>0 |- x::node@v<_,_>.
 print residue.
 //valid
 */
 checkentail x::node@[R]<_,q>*q::ll<n> |- x::ll<m>.
 //fail
 
 checkentail x::node<_,q>*q::ll<n> |- x::ll<m>. 
 print residue.
 //valid
 
 checkentail x::node<_,q>*q::ll<n> |- x::node@v<_,q>*q::ll@v<n>.
 print residue.
 //valid
 
 checkentail x::node<_,q>*q::ll<n> |- x::ll@[R]<m>. 
 print residue.
 // valid

 checkentail x::node@[R]<_,q>*q::ll@[R]<n> |- x::ll@[R]<m>. 
 print residue.
 // valid
 
 
 checkentail x::node@[R]<_,q>*q::ll<n> |- x::ll@[R]<m>. 
 print residue.
 // valid
 
 checkentail x::node<_,q>*q::ll@[R]<n> |- x::ll@[R]<m>. 
 print residue.
 // valid
 
 checkentail x::node<_,q>*q::ll@[R]<n> |- x::ll@[L]<m>. 
  //fail

