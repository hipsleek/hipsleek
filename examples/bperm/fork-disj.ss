
void fun(int test,ref int x)
  requires true
  ensures test=0 & x'=1
      or test!=0 & x'=2;
{
  if (test==0){
    x=1;
  }else{
    x=2;
  }
}

void main(ref int x, ref int y, int test)
  requires true
  ensures test=0 & x'=1 & y'=1
  or test!=0 & x'=2 & y'=2;
{
  int id1 = fork(fun,test,x);
  int id2 = fork(fun,test,y);
  //dprint;
  join(id1);
  join(id2);
  //dprint;
}
