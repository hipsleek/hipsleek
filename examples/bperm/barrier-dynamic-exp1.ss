/*
 Example for dynamic barriers
 */

//permission rules for dynamic barrier
//********************************************
//********************************************
lemma "D-SPLIT" self::barrier(c,t,a)<p> & 0<c<=t+a & c=c1+c2 & a=a1+a2 & 0<c1<t+a1 & 0<c2<t+a2 -> self::barrier(c1,t,a1)<p> * self::barrier(c2,t,a2)<p>;

lemma "D-FULL" self::barrier(c,t,a)<p> & c=t+a & a!=0 -> self::barrier(c,t+a,0)<p>;

//combine successfully
lemma "D-COMBINE-1" self::barrier(c1,t,a1)<p> * self::barrier(c2,t,a2)<p> & c1!=0 & c2!=0 -> self::barrier(c1+c2,t,a1+a2)<p>;

//combine successfully, ordering is not important
lemma "D-COMBINE-2" self::barrier(c1,t,a1)<p1> * self::barrier(c2,t,a2)<p2> & c1!=0 & c2=0 & p2<=p1 -> self::barrier(c1,t,a1+a2)<p1>;

//combine successfully
lemma "D-COMBINE-3" self::barrier(0,t,a1)<p1> * self::barrier(0,t,a2)<p2> -> self::barrier(0,t,a1+a2)<p> & p=max(p1,p2);


//detect inconsistency
lemma "D-FAIL-1" self::barrier(c1,t,a1)<p1> * self::barrier(c2,t,a2)<p2> & c1!=0 & c2!=0 & p1!=p2 -> true & flow __Fail;

//detect inconsistency
lemma "D-FAIL-2" self::barrier(c1,t,a1)<p1> * self::barrier(c2,t,a2)<p2> & c1!=0 & c2=0 & p1<p2 -> true & flow __Fail;

//D-SEP is not implemented as a lemma
//D-SEP is done automatically in xpure_perm
//"D-SEP" b1::barrier(c1,t,a1)<p> * b2::barrier(c2,t,a2)<p> & (t1!=t2 || c1+c2>t1+a1+a2  -> b1!=b2.

//********************************************
//********************************************

// WRAPPER FUNCTION
void destroyBarrier(ref barrier b)
  requires b::barrier(c,t,a)<_> & c=t+a
  ensures b'=null;//'

// WRAPPER FUNCTION
barrier newBarrier(int bound)
  requires bound>0
  ensures res::barrier(bound,bound,0)<0>;

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

//SUCCESS
void thread1(barrier b)
  requires b::barrier(1,3,0)<0>
  ensures b::barrier(1,3,0)<2>;
{
  //phase 0
  waitBarrier(b);
  //phase 1
  waitBarrier(b);
  //phase 2
}

//SUCCESS
void thread2(barrier b)
  requires b::barrier(1,3,0)<0>
  ensures b::barrier(0,3,-1)<1>;
{
  //phase 0
  waitBarrier(b);
  //phase 1
  removeParticipant(b,1);
}

//SUCCESS
void thread3(barrier b)
  requires b::barrier(1,3,0)<0>
  ensures b::barrier(0,3,-1)<0>;
{
  //phase 0
  removeParticipant(b,1);
}

//SUCCESS
void main()
  requires emp & flow __norm
  ensures emp & flow __norm;
{
  barrier b = newBarrier(2);
  addParticipant(b,1);
  int id1 = fork(thread1,b);
  int id2 = fork(thread2,b);
  int id3 = fork(thread3,b);
  //dprint;
  join(id1);
  join(id2);
  join(id3);
  //dprint;
  destroyBarrier(b);
  //dprint;
}
