relation R(int x,int y,int a,int b).

void loo (int x, int y)
infer [@term]
case {
   x+y < 0 -> ensures true;
   x+y = 0 -> ensures true;
   x+y > 0 -> ensures true;
}
{
  if (x>0) {
   x = x+x+y; 
    y = y - 1;
    loo(x,y);
  };
}

/*
# ex27d3.ss 

infer [@term]
case {
   x+y < 0 -> ensures true;
   x+y = 0 -> ensures true;
   x+y > 0 -> ensures true;
}


==>

Procedure loo: FALSE - Counterexample:  {call 14:4}
 case {
   x<=((0-y)-1) & x<=0 -> requires emp & Term[63,1]
                          ensures true & (y+x)<0;
                          
                            
   1<=x & x<=((0-y)-1) -> 
   requires emp & Term[63,2,-1+(1*x)+(0*y)]
   ensures true & (y+x)<0;
   
     
   x=0-y & 0<=y -> requires emp & Term[63,1]
                   ensures true & y+x=0;
                   
                     
   x=0-y & y<=(0-1) -> requires emp & Term[63,3]
                       ensures true & y+x=0;
                       
                         
   ((0-y)+1)<=x & x<=0 -> requires emp & Term[63,1]
                          ensures true & 0<(y+x);
                          
                            
   1<=(y+x) & 1<=x -> requires emp & Loop{call 14:4}[]
                      ensures false & false;
                      
                        
   }

 */
