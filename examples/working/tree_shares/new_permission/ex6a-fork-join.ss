data cell {int val;}

macro L == (#,)
macro R == (,#)
macro LL == ((#,),)
macro LR == ((,#),)
macro RL == (,(#,))
macro RR == (,(,#))

void thread1(cell x, ref int y)
  requires x::cell(@@L)<n>
  ensures x::cell(@@L)<n> & y' = n+1;//'
{
  y=x.val+1;
}


void thread2(cell x, ref int z)
  requires x::cell(@@R)<n>
  ensures x::cell(@@R)<n> & z' = n-1;//'
{
  z=x.val-1;
}

void main(cell x)
  requires x::cell<n>
  ensures x::cell<n>;
{
  int y,z;
  int id1 = fork(thread1,x,y);
  int id2 = fork(thread2,x,z);
  join(id1);
  join(id2);
}
