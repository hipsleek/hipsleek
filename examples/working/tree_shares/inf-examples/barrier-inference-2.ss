data cl {int val;}

barrier bn, 2,  a b c d;  //shared var list


f1(cl x, cl y, cl z, cl d, bn b)   
{
  barrier b;
   x=y+z;                 // does it take the whole y or part of it?  // what happens to d? -> should remain in place, unchanged
  barrier b;
}


f1(cl x, cl y, cl z,cl d, bn b)
{
  barrier b;
   x=z+2;  
  barrier b;
}

