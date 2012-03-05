/*
  Local variables can not escape from its scope via threads.
  Detected by syntactic checking.
  Only pass-by-ref parameters can be mentioned in the post-conditions.
 */

//valid
void inc(ref int i)
requires @full[i]
ensures @full[i] & i'=i+1; //'
{
  i++;
}

//invalid
int scope()
  requires true 
  ensures (exists x: res=z
           and @full[x] & x'=1 & thread=z); //'
{
  int id;
  int x=0;
  id=fork(inc,x); 
  return id; 
}

void main()
  requires true
  ensures true;
{
  int id;
  int i;
  id = scope();
  join(id);
}
