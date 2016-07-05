/*

  Description: Inter-procedural passing 
  of stack variables between concurrent threads

  Variable permissions are automatically inferred.
 */

void inc(ref int i, int j)
  requires true //@full[i] & @value[j]
  ensures i'=i+j; //'@full[i]
{
  i=i+j;
}

int creator(ref int x,ref int y)
  requires true // @full[x] & @full[y]
  ensures y'=y+2 & res=tid //& @full[y]
          and x'=x+1 & thread=tid; //'& @full[x] 
{
  int id;
  id=fork(inc,x,1);
  inc(y,2);
  return id;
}

void main()
requires true ensures true;
{
  int id;
  int x,y;
  x=0;y=0;
  id = creator(x,y);
  join(id);
  assert (x'+y'=3);
}
