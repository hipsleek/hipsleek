/*
  v@value
  b@full
 */

//valid
void inc(ref int i, int j)
requires @full[i] & @value[j]
ensures @full[i] & i'=i+j; //'
{
  //dprint;
  i=i+j;
  //dprint;
}

void testjoin(int id, ref int x)
  requires [i] @value[id]
           and @full[x] & x'=i & thread=id //'
  ensures @full[x] & x'=i; //'
{
  //not specified in the main thread -> zero
  //we may need to check for consistency of var permissions
  // among thread
  //we need to add @zero[x] here
  join(id);
}

//BUG
int main()
requires true
  ensures res=2;
{
  int id;
  int x,y;
  x=0;y=1;
  id = fork(inc,x,y);
  //inc(x,y);
  dprint;
  testjoin(id,x); 
  //join(id);
  dprint;
  return x+y;
}
