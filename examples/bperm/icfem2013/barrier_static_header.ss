/*

  Header for static barriers

  (Defined in Fig. 6. Verification of Static Barriers)

 */

//permission rules for static barriers
//********************************************
lemma "S-SPLIT" self::barrier(c,t,0)<p> & 0<c<=t & c=c1+c2 & 0<c1<t & 0<c2<t -> self::barrier(c1,t,0)<p> * self::barrier(c2,t,0)<p>;

//combine successfully
lemma "S-COMBINE" self::barrier(c1,t,0)<p> * self::barrier(c2,t,0)<p> -> self::barrier(c1+c2,t,0)<p>;

//S-SEP is done automatically of the verifier
//********************************************

// WRAPPER FUNCTION
barrier newBarrier(int bound)
  requires bound>0
  ensures res::barrier(bound,bound,0)<0>;

// WRAPPER FUNCTION
void destroyBarrier(ref barrier b)
  requires b::barrier(c,t,0)<_> & c=t
  ensures b'=null;//'

// WRAPPER FUNCTION
void waitBarrier(barrier b)
  requires b::barrier(c,t,0)<p> & c=1
  ensures b::barrier(c,t,0)<p+1>;
//********************************************
