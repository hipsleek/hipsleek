data cl {int val;}

barrier bn, 2,x1 x2 y1 y2 i,[(0,1,[
 requires x1::cl@[L]<A1>*x2::cl@[L]<B1>*y1::cl@[L]<C1>*y2::cl@[L]<D1>*i::cl@[L]<T1>*self::bn@[L]<0> 
        ensures x1::cl@[L]<A1>*x2::cl@[L]<B1>*y1::cl<C1>*i::cl@[L]<T1>*self::bn@[L]<1>;,
 requires x1::cl@[R]<A2>*x2::cl@[R]<B2>*y1::cl@[R]<C2>*y2::cl@[R]<D2>*i::cl@[R]<T2>*self::bn@[R]<0>
        ensures x1::cl@[R]<A2>*x2::cl@[R]<B2>*y2::cl<D2>*i::cl@[R]<T2>*self::bn@[R]<1>;]),	
 (1,2,[
 requires x1::cl@[L]<A>*x2::cl@[L]<A>*y1::cl<C>*i::cl@[L]<T>*self::bn@[L]<1>&T<30 & A=2*T-1 & C = 3*A+2
    ensures x1::cl<A>*y1::cl@[L]<C>*y2::cl@[L]<D>*i::cl<T>*self::bn@[L]<2>&T<30 & A=2*T-1 & D=2*A & C = 3*A+2;,
 requires x1::cl@[R]<A>*x2::cl@[R]<A>*y2::cl<D>*i::cl@[R]<T>*self::bn@[R]<1>&T<30 & D=2*A & A=2*T-1
    ensures x2::cl<A>*y1::cl@[R]<C>*y2::cl@[R]<D>*         self::bn@[R]<2> & D=2*A & C = 3*A+2 & A=2*T-1;]),
    
 (2,1,[
 requires x2::cl<B>*y1::cl@[R]<C>*y2::cl@[R]<D>*         self::bn@[R]<2> & B=C-D
    ensures x1::cl@[R]<A>*x2::cl@[R]<B>*y2::cl<D>*i::cl@[R]<T>*self::bn@[R]<1> & A=C-D & A=B & A=2*T-1 & T <= 30;,
 requires x1::cl<A>*y1::cl@[L]<C>*y2::cl@[L]<D>*i::cl<T>*self::bn@[L]<2> & A=C-D & A=2*T-1 & T <= 30
    ensures x1::cl@[L]<A>*x2::cl@[L]<B>*y1::cl<C>*i::cl@[L]<T>*self::bn@[L]<1> & A=C-D & A=B & A=2*T-1 & T <= 30;]) ,
 
 (1,3,[
 requires x1::cl@[L]<A>*x2::cl@[L]<B>*i::cl@[L]<T>*self::bn@[L]<1>& T=30 
    ensures x1::cl@[L]<A>*x2::cl@[L]<B>*i::cl<T>*self::bn@[L]<3> & T=30;, 
 requires x1::cl@[R]<A>*x2::cl@[R]<B>*i::cl@[R]<T>*self::bn@[R]<1>& T=30 
    ensures x1::cl@[R]<A>*x2::cl@[R]<B>         *self::bn@[R]<3>;])];

 
void th2 (cl x1, cl x2, cl y1, cl y2, cl i, bn b)
requires x1::cl@[R]<1>*x2::cl@[R]<1>*y1::cl@[R]<_>*y2::cl@[R]<_>*i::cl@[R]<1>*b::bn@[R]<0> 
 ensures x1::cl@[R]<v>*x2::cl@[R]<v>*b::bn@[R]<3>& v=59; //2*q-1 & q>=30;
{                                 // stage 0
  barrier b;                      // stage 0->1
  while(i.val<30)
  requires x1::cl@[R]<v>*x2::cl@[R]<v>*y2::cl<_>*i::cl@[R]<a>*b::bn@[R]<1> & v=2*a -1 & a <= 30
 // ensures x1::cl@[R]<v1>*x2::cl@[R]<v1>*b::bn@[R]<3>& v1=59; //2*q-1 & q>=30;
  ensures x1::cl@[R]<v1>*x2::cl@[R]<v1>*i::cl@[R]<a>*b::bn@[R]<2>& v1=2*a-1 & a=30;
  {                              // stage 1
    y2.val = x1.val + x2.val;
    barrier b;                    // stage 1->2
    x2.val = y1.val - y2.val;
    barrier b;                    // stage 2->1
  }
  barrier b;                      // stage 1->3
}
  
void th1 (cl x1, cl x2, cl y1, cl y2, cl i, bn b)
requires x1::cl@[L]<1>*x2::cl@[L]<1>*y1::cl@[L]<_>*y2::cl@[L]<_>*i::cl@[L]<1>*b::bn@[L]<0> 
 ensures x1::cl@[L]<v>*x2::cl@[L]<v>*b::bn@[L]<3>& v=59; // 2*q-1 & q>=30;
{                                 // stage 0
  barrier b;                      // stage 0->1
  while (i.val<30)
  requires x1::cl@[L]<v>*x2::cl@[L]<v>*y1::cl<_>*i::cl@[L]<a>*b::bn@[L]<1> & v=2*a -1 & a <= 30
  ensures x1::cl@[L]<v1>*x2::cl@[L]<v1>*i::cl@[L]<a>*b::bn@[L]<2>& v1=2*a-1 & a=30;
  {                               // stage 1
    y1.val = x1.val + 2*x2.val+2;
    barrier b;                    // stage 1->2
    x1.val = y1.val - y2.val;
    i.val= i.val+1;
    barrier b;                    // stage 2->1
  }
  barrier b;                      // stage 1->3
}