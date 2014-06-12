/*

  Description: fairly complicated inter-procedural passing 
  of stack variables between concurrent threads

 */

void inc(ref int i, int j)
 requires emp
 ensures  emp & i'=i+j; //'
 /* requires @full[i] & @value[j] */
 /* ensures  i'=i+j & @full[i']; //' */
{
  i=i+j;
}

thrd creator(ref int x,ref int y)
  requires emp
  ensures res::thrd<# emp & x'=x+1 #> & y'=y+2; //'
  /* requires @full[x] & @full[y] */
  /* ensures res::thrd<# emp & x'=x+1 & @full[x'] #> & y'=y+2 & @full[y']; //' */
{
  thrd id;
  id=fork(inc,x,1);
  inc(y,2);
  return id;
}

void main()
  requires emp
  ensures emp;
{
  thrd id;
  int x,y;
  x=0;y=0;
  id = creator(x,y);
  join(id);
  assert(x'+y'=3);
}
