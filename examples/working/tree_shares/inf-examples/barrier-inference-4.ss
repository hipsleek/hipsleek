data cl {int val;}

barrier bn, 2,  a b c d;  //shared var list


f1(cl x, cl y, cl z, cl d, bn b)   
{
  barrier b;
   if (y.val>30) then       
                    // based on this thread, it is not strictly necessary to have different barrier states for line 12 and 18
                    // could be usefull in conjunction with the postcondition to be proven but this is a stronger property than what we want
      {
          d=z+1;
          barrier b;
          x=y+z+1;
      }
   else 
      {
          d=z+2;
          barrier b;
          x=y+z+2;
      }
  barrier;
}