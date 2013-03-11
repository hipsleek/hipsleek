/*
  Simple examples of variable permissions with global variables
 */
global int g;

//increase 'i' with an amount 'g'
void inc(ref int i)
  requires @full[i]
  ensures  @full[i] & i'=i+g; //'
{
  i = i + g;
}

//race in "g" --> fail
void func()
requires g=1
  ensures true;
{
  int x,y;
  x=0;y=0;
  int id1 = fork(inc,x);
  inc(y); // not allow because the child thread is holding the full
  // permission of the global variable "g" --> FAIL
  join(id1);
  assert x'=g & y'=g;
}
