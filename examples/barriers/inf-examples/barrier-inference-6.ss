data cl {int val;}

barrier bn, 2,  a b c d;  //shared var list


f1(cl x, cl y, cl z, cl d, bn b)   
{
  while (d>0)                         // the code finished with one loop, the barrier could either have two loops or just one?
  {
        x=y-2;
      barrier b;
        y=x-2;
        d=d-1;
      barrier b;
  }
  // maybe some other code here
  while (d>-10)
  {
        x=y-3;
      barrier b;
        y=x-3;
        d=d-2;
      barrier b;
  }
}