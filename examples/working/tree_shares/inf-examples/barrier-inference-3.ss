data cl {int val;}

barrier bn, 2,  a b c d;  //shared var list


f1(cl x, cl y, cl z, cl d, bn b)   
{
  int a = x.val;
  barrier b;
      // x is taken completely , possibly to be modified by other threads
  barrier b;
      // can i act on a? yes, now it is just a local var
   if (a>30) then
      {
          barrier b;
          x=y+z;          
      }
   else 
      {
          barrier b;
          d=x+z;
      }
  barrier;
}