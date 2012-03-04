/*
  Checking for variable permissions 
  in the presence of concurrent threads
 */

data cell{
  int val;
}

//valid
void inc(ref int i)
  requires @full[i]
  ensures @full[i];
{
  i++;
}

void inc(ref cell i)
  requires @full[i]
  ensures @full[i]; //check for permission only
{
  int j;
}

//fail
int test1(ref int x,ref int y)
  requires @full[x,y]
  ensures @full[y] & res = z
          and @full[x] & thread=z; //'
{
  int id;
  id=fork(inc,x);
  dprint;
  x = 0; // --> Assign: fail
  dprint;
  inc(y);
  return id;
}

//fail
int test2(ref cell x,ref cell y)
  requires x::cell<i> * y::cell<j> & @full[x,y] 
  ensures y::cell<j+1> & @full[y] & res = z
          and x::cell<i+1> & @full[x] & thread=z; //'
{
  int id;
  id=fork(inc,x);
  dprint;
  y.val ++;
  x.val++; // --> Bind: fail
  return id;
}

//fail
int test3(ref int x,ref int y)
  requires @full[x,y]
  ensures @full[y] & res = z
          and @full[x] & thread=z; //'
{
  int id;
  id=fork(inc,x);
  dprint;
  y = x; // --> Var: fail
  inc(y);
  return id;
}

//fail
int test4(ref int x,ref int y)
  requires @full[x,y]
  ensures @full[y] & res = z
          and @full[x] & thread=z; //'
{
  int id;
  id=fork(inc,x);
  dprint;
  inc(y);
  return x; // --> Sharp_var: fail
}
