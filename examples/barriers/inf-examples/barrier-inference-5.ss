data cl {int val;}

barrier bn, 2,  a b c d;  //shared var list


f1(cl x, cl y, cl z, cl d, bn b)   
{
  barrier b;
   if (y.val>30) then       
      {
          d=z+1;
          barrier b;                              // states in 12 and 29 can be the same
          if  (y<40) then
            {
                y=....;
                barrier b;                      // 16 and 22 could differ , also 33 and 39 could differ
                x=2;
            }
          else
            {
                y=.....'
                barrier b;
                d= 2;
            }
      }
   else 
      {
           d=z+1;
          barrier b;                              // states in 12 and 29 can be the same
          if  (y<40) then
            {
                y=....;
                barrier b;                        // 16 and 22 could differ , also 33 and 39 could differ
                x=2;
            }
          else
            {
                y=.....'
                barrier b;
                d= 2;
            }
      }
  
}