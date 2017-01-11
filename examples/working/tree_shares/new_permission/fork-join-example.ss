/*
Motivating example for bperm
*/

data cell {int val;}
macro L == (#,)
macro R == (,#)

void thread1(cell x, ref int y)
requires x::cell(@@L)<5>
ensures x::cell(@@L)<5> & y'=6;//'
{
   y=x.val+1;
}

void thread2(cell x, ref int z)
requires x::cell(@@R)<5>
ensures x::cell(@@R)<5> & z'=4;//'
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
requires true
ensures true;
{
  cell x;
  int y,z,t;
  x.val = 5;
  int id1 = fork(thread1,x,y);//thread1 accesses x
  int id2 = fork(thread2,x,z);//thread2 accesses x
  int id3 = fork(thread3,x,t);//thread3 DOES NOT
  join(id1);
  join(id2);
  join(id3);
  int tmp = x.val;
  assert(tmp'=5);
  // destroyCell(x);
  assert(y'=6 & z'=4 & t'=10);
}
