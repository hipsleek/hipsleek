data cl {int val;}.

checkentail x::cl<n> & n > 3 |- x::cl<m> & m > 2.
checkentail x::cl<n> & n > 1 |- x::cl<m> & m > 2.

checkentail x::cl<_> |- x::cl<_>.

checkentail x::cl@[L,R]<_> |- x::cl<_>.
checkentail x::cl@[L,R]<_> |- x::cl@[L]<_>.
checkentail x::cl@[L]<_> |- x::cl@[R]<_>.
checkentail x::cl<_> |- x::cl@[R]<_>.
print residue.
checkentail x::cl<_> |- x::cl@[L]<_>.
print residue.


checkentail x::cl@[L,R]<_> |- x::cl<_>.
checkentail x::cl@[R,R]<_> |- x::cl[L,R]<_>.
checkentail x::cl@v<_> |- x::cl@v<_>.

checkentail x::cl@v1<_> |- x::cl@v<_>. 

checkentail x::cl@[R]<_> |- x::cl@[R,L]<_>.
print residue.


checkentail x::cl@[L]<_> * x::cl@[R]<_>|- x::cl<_>.

checkentail x::cl@[L]<_> * x::cl@[R]<_>|- x::cl@v<_>.
print residue.

checkentail x::cl@[L]<_> * x::cl@[R]<_>|- x::cl@v<_> & join([L],[R,L],v).
print residue.

checkentail x::cl@[L]<_> * x::cl@[R]<_>|- x::cl@v<_> & join ([L],[R,L],v).

checkentail x::cl@[L]<_> * x::cl@[R]<_>|- x::cl@v<_> & join ([R],[R,L],v).

checkentail x::cl@v<_> &join ([L],[L,R],v)|- x::cl@v<_> & join ([R],[R,L],v).

checkentail x::cl@[L]<_> * x::cl@[R]<_>|- 1>2.

checkentail x::cl@[L]<_> * x::cl@[L,R]<_>|- 1>2.

/*
barrier b1n, 2,[(0,1,[
 requires x1::cl@[L]<A>*x2::cl@[L]<B>*y1::cl@[L]<C>*y2::cl@[L]<D>*i::cl@[L]<T>*self::b1n@[L]<0> ensures x1::cl@[L]<A>*x2::cl@[L]<B>*y1::cl<C>*i::cl@[L]<T>*self::b1n@[L]<1> ,
 requires x1::cl@[R]<A>*x2::cl@[R]<B>*y1::cl@[R]<C>*y2::cl@[R]<D>*i::cl@[R]<T>*self::b1n@[R]<0> ensures x1::cl@[R]<A>*x2::cl@[R]<B>*y2::cl<D>*i::cl@[R]<T>*self::b1n@[R]<1>]),	
 (1,2,[
 requires x1::cl@[L]<A>*x2::cl@[L]<B>*y1::cl<C>*i::cl@[L]<T>*self::b1n@[L]<1>&T<30 ensures x1::cl<A>*y1::cl@[L]<C>*y2::cl@[L]<D>*i::cl<T>*self::b1n@[L]<2>&T<30,
 requires x1::cl@[R]<A>*x2::cl@[R]<B>*y2::cl<D>*i::cl@[R]<T>*self::b1n@[R]<1>&T<30 ensures x2::cl<B>*y1::cl@[R]<C>*y2::cl@[R]<D>*         self::b1n@[R]<2>]),
 (2,1,[
 requires x2::cl<B>*y1::cl@[R]<C>*y2::cl@[R]<D>*         self::b1n@[R]<2> ensures x1::cl@[R]<A>*x2::cl@[R]<B>*y2::cl<D>*i::cl@[L]<T>*self::b1n@[R]<1>,
 requires x1::cl<A>*y1::cl@[L]<C>*y2::cl@[L]<D>*i::cl<T>*self::b1n@[L]<2> ensures x1::cl@[L]<A>*x2::cl@[L]<B>*y1::cl<C>*i::cl@[L]<T>*self::b1n@[L]<1> ,
 (1,3,[
 requires x1::cl@[L]<A>*x2::cl@[L]<B>*i::cl@[L]<T>*self::b1n@[L]<1>& T>=30 ensures x1::cl@[L]<A>*x2::cl@[L]<B>*i::cl<T>*self::b1n@[L]<3> & T>=30, 
 requires x1::cl@[R]<A>*x2::cl@[R]<B>*i::cl@[R]<T>*self::b1n@[R]<1>& T>=30 ensures x1::cl@[R]<A>*x2::cl@[R]<B>         *self::b1n@[R]<3>
 ])].*/