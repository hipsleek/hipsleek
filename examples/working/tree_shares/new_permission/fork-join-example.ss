/*
Motivating example for bperm
*/

data cell {int val;}
macro L == (#,)
macro R == (,#)

void thread1(cell x, ref int y)
requires x::cell(@@L)<n>
ensures x::cell(@@L)<n> & y'=n+1;//'
{
   y=x.val+1;
}


void thread2(cell x, ref int z)
requires x::cell(@@L)<n>
ensures x::cell(@@L)<n> & z'= n-1;//'
{
 z=x.val-1;
 }


void thread3(cell x, ref int t)
requires true
ensures t'=10;//'
{
 t=10;
 }


void test(cell x, ref int y, ref int z, ref int t)
requires x::cell<n>
ensures x::cell<n> & y' = y + 1 & z' = z - 1 & t' = 10;
{
  int id1 = fork(thread1,x,y);//thread1 accesses x
  int id2 = fork(thread2,x,z);//thread2 accesses x
  int id3 = fork(thread3,x,t);//thread3 DOES NOT
  join(id1);
  join(id2);
  join(id3);
//  int tmp = z + 2;
//  assert(tmp' = x.val + 1);
  // destroyCell(x);
 // assert(y'=6 & z'=4 & t'=10);
}
