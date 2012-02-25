/*

  Description: fairly complicated inter-procedural passing 
  of stack variables between concurrent threads

 */

void inc(ref int i)
requires @full[i]
ensures @full[i] & i'=i+1; //'
{
  i++;
}

int creator(ref int x,ref int y)
  requires @full[x] & @full[y]
  ensures @full[y] & y'=y+1 & res=z
          and @full[x] & x'=x+1 & thread=z; //'
{
  int id;
  id=fork(inc,x);
  inc(y);
  return id;
}

void joiner(int id, ref int x)
  requires [i] @value[id]
           and @full[x] & x'=i+1 & thread=id //'
  ensures @full[x] & x'=i+1; //'
{
  join(id);
}


int main()
requires true
  ensures res=2;
{
  int id;
  int x,y;
  x=0;y=0;
  id = creator(x,y);
  joiner(id,x); 
  return x+y;
}
