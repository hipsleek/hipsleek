/*
  Checking for variable permissions 
  in the presence of concurrent threads.
 */

data cell{
  int val;
}

//valid
void inc(ref int i)
  requires true //@full[i]
  ensures true; //@full[i]; //' check for VPERM only
{
  i++;
}

void incCell(ref cell x)
  requires x::cell<i> //& @full[x]
  ensures x::cell<i+1> ; //& @full[x]; //check for permission only
{
  x.val++;
}

//fail
int test1(ref int x,ref int y)
  requires true //@full[x,y]
  ensures @full[y] & res = z
          and @full[x] & thread=z; //'
{
  int id;
  id=fork(inc,x);
  x = 0; // --> No permission -> cannot assign to x
  inc(y);
  return id;
}

//fail
int test2(ref cell x,ref cell y)
  requires x::cell<i> * y::cell<j> // & @full[x,y] 
  ensures y::cell<j+1> & @full[y] & res = z
          and x::cell<i+1> & @full[x] & thread=z; //'
{
  int id;
  id=fork(incCell,x);
  y.val ++;
  x.val++; // --> No permission -> cannot access its field
  return id;
}

//fail
int test3(ref int x,ref int y)
  requires true //@full[x,y]
  ensures @full[y] & res = z
          and @full[x] & thread=z; //'
{
  int id;
  id=fork(inc,x);
  y = x; // --> No permission -> cannot read x
  inc(y);
  return id;
}

//fail
int test4(ref int x,ref int y)
  requires true //@full[x,y]
  ensures @full[y] & res = z
          and @full[x] & thread=z; //'
{
  int id;
  id=fork(inc,x);
  inc(y);
  return x; // --> No permission -> cannot return x
}
