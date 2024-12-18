/*

  Header for dynamic barriers

  (Defined in Fig. 8. Verification of Dynamic Barriers)

 */

//permission rules for dynamic barriers
//********************************************
//********************************************
lemma "D-SPLIT" self::barrier(c,t,a)<p> & 0<c<=t+a & c=c1+c2 & a=a1+a2 & 0<c1<t+a1 & 0<c2<t+a2 & a1*c=c1*a & a2*c=c2*a -> self::barrier(c1,t,a1)<p> * self::barrier(c2,t,a2)<p>;

//combine successfully
lemma "D-COMBINE-1" self::barrier(c1,t,a1)<p> * self::barrier(c2,t,a2)<p> & c1!=0 & c2!=0 -> self::barrier(c1+c2,t,a1+a2)<p>;

//combine successfully, ordering is not important
lemma "D-COMBINE-2" self::barrier(c1,t,a1)<p1> * self::barrier(c2,t,a2)<p2> & c1!=0 & c2=0 & p2<=p1 -> self::barrier(c1,t,a1+a2)<p1>;

//combine successfully
lemma "D-COMBINE-3" self::barrier(0,t,a1)<p1> * self::barrier(0,t,a2)<p2> -> self::barrier(0,t,a1+a2)<p> & p=max(p1,p2);

lemma "D-FULL" self::barrier(c,t,a)<p> & c=t+a & a!=0 & c>0 -> self::barrier(c,t+a,0)<p>;

//D-SEP is done automatically by the verifier
//"D-SEP" b1::barrier(c1,t,a1)<p1> * b2::barrier(c2,t,a2)<p2> & (t1!=t2 || c1+c2>t1+a1+a2  -> b1!=b2.

//********************************************
//********************************************

// WRAPPER FUNCTION
barrier newBarrier(int bound)
  requires bound>0
  ensures res::barrier(bound,bound,0)<0>;

// WRAPPER FUNCTION
void destroyBarrier(ref barrier b)
  requires b::barrier(c,t,a)<_> & c=t+a
  ensures b'=null;//'

// WRAPPER FUNCTION
void waitBarrier(barrier b)
  requires b::barrier(c,t,a)<p> & c=1
  ensures b::barrier(c,t,a)<p+1>;

// WRAPPER FUNCTION
void addParticipant(barrier b,int m)
  requires b::barrier(c,t,a)<p> & c>0 & m>0
  ensures b::barrier(c+m,t,a+m)<p>;

// WRAPPER FUNCTION
void removeParticipant(barrier b,int m)
  requires b::barrier(c,t,a)<p> & c>=m & m>0
  ensures b::barrier(c-m,t,a-m)<p>;
//********************************************
