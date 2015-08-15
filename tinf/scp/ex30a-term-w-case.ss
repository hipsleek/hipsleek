
relation R(int xxx,int y,int a,int b).

void loo (ref int xxx, ref int y,int a, int b)
  infer [@term_wo_post]
  requires true
  ensures true;
/*
 case {
  xxx>0 | y>0 -> ensures true;
  xxx<=0 & y<=0 -> ensures true;
  }
*/
{

  if (xxx>0 || y>0) {
    //dprint;
    xxx = xxx+a-b-1;
    y = y+b-a-1;
    loo(xxx,y,a,b);
  };
}

/*
# ex30a.ss 

# why are there still post when we used @term_wo_post?
# they seem inaccurate..

  y<=0 & 1<=x -> 
   case {
     b<a -> requires emp & Loop{call 16:4}[]
            ensures false & false;
            
              
     b=a -> 
     requires emp & Term[64,2,0+(1*x)+(0*y)+(0*a)+(0*b)]
     ensures true & (0<x | 0<y);
     
       
     a<b -> requires emp & MayLoop[]
            ensures true & (0<x | 0<y);
 

Procedure loo: FALSE - Counterexample:  {call 16:4}
 case {
   y<=0 & 1<=x -> 
   case {
     b<a -> requires emp & Loop{call 16:4}[]
            ensures false & false;
            
              
     b=a -> 
     requires emp & Term[64,2,0+(1*x)+(0*y)+(0*a)+(0*b)]
     ensures true & (0<x | 0<y);
     
       
     a<b -> requires emp & MayLoop[]
            ensures true & (0<x | 0<y);
            
              
     }
     
   1<=y & 1<=x -> 
   case {
     a!=b -> requires emp & Loop{call 16:4}[]
             ensures false & false;
             
               
     b=a -> 
     requires emp & Term[64,4,0+(0*x)+(1*y)+(0*a)+(0*b)]
     ensures true & (0<x | 0<y);
     
       
     }
     
   x<=0 & 1<=y -> 
   case {
     a<b -> requires emp & Loop{call 16:4}[]
            ensures false & false;
            
              
     a=b -> 
     requires emp & Term[64,3,0+(0*x)+(1*y)+(0*a)+(0*b)]
     ensures true & (0<x | 0<y);
     
       
     b<a -> requires emp & MayLoop[]
            ensures true & (0<x | 0<y);
            
              
     }
     
   x<=0 & y<=0 -> requires emp & Term[64,1]
                  ensures true & y<=0 & x<=0;
                  


*/
