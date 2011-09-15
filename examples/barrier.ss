data cl {int val;}

barrier bn, 2,x1 x2 y1 y2 i,[(0,1,[
 requires x1::cl@[L]<A>*x2::cl@[L]<A>*y1::cl@[L]<A>*y2::cl@[L]<C>*i::cl@[L]<A>*self::bn@[L]<0> 
   ensures x1::cl@[L]<A>*x2::cl@[L]<A>*y1::cl<A>*i::cl@[L]<A>*self::bn@[L]<1>;,
 requires x1::cl@[R]<B>*x2::cl@[R]<B>*y1::cl@[R]<B>*y2::cl@[R]<C>*i::cl@[R]<B>*self::bn@[R]<0> 
   ensures x1::cl@[R]<B>*x2::cl@[R]<B>*y2::cl<C>*i::cl@[R]<B>*self::bn@[R]<1>;]),	
 (1,2,[
 requires x1::cl@[L]<A>*x2::cl@[L]<A>*y1::cl<A>*i::cl@[L]<A>*self::bn@[L]<1>&A<30 
    ensures x1::cl<A>*y1::cl@[L]<A+1>*y2::cl@[L]<A>*i::cl<A>*self::bn@[L]<2>&A<30;,
 requires x1::cl@[R]<B>*x2::cl@[R]<B>*y2::cl<B>*i::cl@[R]<B>*self::bn@[R]<1>&B<30 
    ensures x2::cl<B>*y1::cl@[R]<B>*y2::cl@[R]<B>*         self::bn@[R]<2>;]),
 (2,1,[
 requires x2::cl<A>*y1::cl@[R]<A+1>*y2::cl@[R]<A>*         self::bn@[R]<2> 
    ensures x1::cl@[R]<A+1>*x2::cl@[R]<>*y2::cl<D>*i::cl@[L]<T>*self::bn@[R]<1>;,
 requires x1::cl<B>*y1::cl@[L]<B+1>*y2::cl@[L]<B>*i::cl<B>*self::bn@[L]<2> 
    ensures x1::cl@[L]<A>*x2::cl@[L]<B>*y1::cl<C>*i::cl@[R]<T>*self::bn@[L]<1>;]) ,
 (1,3,[
 requires x1::cl@[L]<A>*x2::cl@[L]<B>*i::cl@[L]<T>*self::bn@[L]<1>& T>=30 
    ensures x1::cl@[L]<A>*x2::cl@[L]<B>*i::cl<T>*self::bn@[L]<3> & T>=30;, 
 requires x1::cl@[R]<A>*x2::cl@[R]<B>*i::cl@[R]<T>*self::bn@[R]<1>& T>=30 
    ensures x1::cl@[R]<A>*x2::cl@[R]<B>         *self::bn@[R]<3>;])];
 
 
void th1 (cl x1, cl x2, cl y1, cl y2, cl i, bn b)
requires x1::cl@[L]<0>*x2::cl@[L]<0>*y1::cl@[L]<0>*y2::cl@[L]<0>*i::cl@[L]<0>*b::bn@[L]<0> 
 ensures x1::cl@[L]<30>*x2::cl@[L]<30>*y1::cl@[L]<30>*y2::cl@[L]<29>*i::cl@[L]<0>*b::bn@[L]<3>;
{
  barrier b;
  th1_loop (x1,x2,y1,y2,i,b);
}
 
void th1_loop(cl x1, cl x2, cl y1, cl y2, cl i, bn b)
requires x1::cl@[L]<a>*x2::cl@[L]<a>*y1::cl@[L]<a>*i::cl@[L]<a>*b::bn@[L]<1> 
 ensures x1::cl@[L]<30>*x2::cl@[L]<30>*y1::cl@[L]<30>*y2::cl@[L]<29>*i::cl@[L]<0>*b::bn@[L]<3>;
{
  if (i.val<30)
  {
    y1.val = x2.val+1;
    barrier b;
    x1.val = y2.val+1;
    i.val=i.val+1;
    barrier b;
    dprint;
    th1 (x1,x2,y1,y2,i,b);
  }
  else {barrier b; i.val=0;}  
}


/*
void th2(cl x1, cl x2, cl y1, cl y2, cl i, bn b)
requires x1::cl@[L]<0>*x2::cl@[L]<0>*y1::cl@[L]<0>*y2::cl@[L]<0>*i::cl@[L]<0>*b::bn@[L]<0>
ensures true;
{
  barrier b;
  int n=0;
  while (n<30)
  {
    y2.val = x1.val;
    barrier b;
    x2.val = y1.val;
    barrier b;
    n=i.val;
  }
  barrier b;
}
*/