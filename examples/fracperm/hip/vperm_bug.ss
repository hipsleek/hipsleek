/*
  May our mechanism be too restrictive ???

 After passed by ref, x can not escape from the scope
of method main() because it has zero permission.
 */

//valid
void inc(ref int i)
requires @p_ref[i]
ensures @full[i] & i'=i+1; //'
{
  i++;
}

//valid
int testfork(ref int x,ref int y)
  requires @p_ref[x] & @p_ref[y]
  ensures @full[y] & y'=y+1 & res=z
          and @full[x] & x'=x+1 & thread=z; //'
{
  int id;
  dprint;
  id=fork(inc,x);
  dprint;
  inc(y);
  dprint;
  return id;
}

//???
void testjoin(int id, ref int x)
  requires [i] @p_ref[x] & @p_val[id]
           and @full[x] & x'=i+1 & thread=id //'
  ensures @full[x] & x'=i+1; //'
{
  dprint;
  join(id);
  // this join can not be done
  // because we do not have @zero(x) in the estate
  // ???
  dprint;
}

//???
int main()
requires true
  ensures res=2;
{
  int id;
  int x,y;
  x=0;y=0;
  id = testfork(x,y);// ??? since then, x can not escape from main()
  dprint;
  //testjoin(id,x); 
  //Can not pass x by ref here because we have no permission to x
  //May our mechanism be too restrictive ???
  //Should we need a way to pass @zero to a method call
  join(id); //this join is valid because we have @zero[x]
  dprint;
  return x+y;
}
