/*
  Motivating example for bperm
 */

data cell {int val;}

//permission rules for cell
//********************************************
lemma "cell-SPLIT" self::cell(c,t,0)<p> & 0<c<=t & c=c1+c2 & 0<c1<t & 0<c2<t -> self::cell(c1,t,0)<p> * self::cell(c2,t,0)<p>;

lemma "cell-COMBINE" self::cell(c1,t,0)<p> * self::cell(c2,t,0)<p> -> self::cell(c1+c2,t,0)<p>;
//********************************************


// WRAPPER FUNCTION
void destroyCell(ref cell ce)
  requires ce::cell(c,t,a)<_> & c=t+a
  ensures ce'=null;//'

// WRAPPER FUNCTION
cell newCell(int bound,int value)
  requires bound>0
  ensures res::cell(bound,bound,0)<value>;

//

void thread1(cell x, ref int y)
  requires x::cell(1,2,0)<5>
  ensures x::cell(1,2,0)<5> & y'=6;//'
{
  y=x.val+1;
}

void thread2(cell x, ref int z)
  requires x::cell(1,2,0)<5>
  ensures x::cell(1,2,0)<5> & z'=4;//'
{
  z=x.val-1;
}

void thread3(cell x, ref int t)
  requires true
  ensures t'=10;//'
{
  t=10;
}

void main()
  requires emp
  ensures emp;
{
  cell x = newCell(2,0);//only 2 threads are allowed to access x
  int y,z,t;
  x.val = 5;
  int id1 = fork(thread1,x,y);//thread1 accesses x
  int id2 = fork(thread2,x,z);//thread2 accesses x
  int id3 = fork(thread3,x,t);//thread3 DOES NOT
  join(id1);
  join(id2);
  join(id3);
  destroyCell(x);
  assert(y'=6 & z'=4 & t'=10);
}
