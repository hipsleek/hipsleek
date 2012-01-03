/*
  v@value
  b@full
 */

//valid
void inc(ref int i)
requires @full[i]
ensures @full[i] & i'=i+1; //'
{
  i++;
}

//valid
int testfork(ref int x,ref int y)
  requires @full[x] & @full[y]
  ensures @full[y] & y'=y+1 & res=z
          and @full[x] & x'=x+1 & thread=z; //'
{
  int id;
  id=fork(inc,x);
  dprint;
  inc(y);
  dprint;
  return id;
}


void testjoin(int id, ref int x)
  requires [i] @value[id]
           and @full[x] & x'=i+1 & thread=id //'
  ensures @full[x] & x'=i+1; //'
{
  //not specified in the main thread -> zero
  //we may need to check for consistency of var permissions
  // among thread
  //we need to add @zero[x] here
  join(id);
}


int main()
requires true
  ensures res=2;
{
  int id;
  int x,y;
  x=0;y=0;
  id = testfork(x,y);
  dprint;
  //testjoin(id,x); 
  join(id);
  dprint;
  return x+y;
}
