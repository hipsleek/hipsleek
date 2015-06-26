
relation R(int x,int y,int a,int b).

void loo (ref int x, ref int y,int a, int b)
  infer [@term_wo_post]
  requires true
  ensures true;
{

  if (x>0 || y>0) {
    //dprint;
    x = x+a-b-1;
    y = y+b-a-1;
    loo(x,y,a,b);
  };
}

/*
# ex29d1.ss 

# without post
  infer [@term_wo_post]
  requires true
  ensures true;

# Are these non-term ok?

   y<=0 & 1<=x -> 
   case {
     b<a -> requires emp & Loop{call 14:4}[]
            ensures false & false;

   1<=y & 1<=x -> 
   case {
     a!=b -> requires emp & Loop{call 14:4}[]
             ensures false & false;

   x<=0 & 1<=y -> 
   case {
     a<b -> requires emp & Loop{call 14:4}[]
            ensures false & false;


Procedure loo: FALSE - Counterexample:  {call 14:4}
 requires true & true
 case {
   y<=0 & x<=0 -> requires emp & Term[64,1]
                  ensures true & true;
                  
                    
   y<=0 & 1<=x -> 
   case {
     b<a -> requires emp & Loop{call 14:4}[]
            ensures false & false;
            
              
     b=a -> 
     requires emp & Term[64,2,-1+(1*x)+(0*y)+(0*a)+(0*b)]
     ensures true & true;
     
       
     a<b -> 
     case {
       (((y<=0 & 1<=x & (2+a)<=(y+b)) | (a<b & (2+b)<=(x+a) & (y+b)<=(1+a)))) & 
       (((y<=0 & 1<=x & (2+a)<=(y+b)) | 
         ((y+b)<=(1+a) & (2+b)<=(x+a) & (3+(2*a))<=(y+(2*b))) | 
         (a<b & (3+(2*b))<=(x+(2*a)) & (y+(2*b))<=(2+(2*a))))) & 
       (((y<=0 & (x+(3*a))<=(3+(3*b)) & (3+(2*b))<=(x+(2*a)) & 
          (y+(3*b))<=(3+(3*a))) | 
         (y<=0 & 1<=x & (2+a)<=(y+b)) | 
         ((2+b)<=(x+a) & (y+b)<=(1+a) & (3+(2*a))<=(y+(2*b))) | 
         ((y+(2*b))<=(2+(2*a)) & (3+(2*b))<=(x+(2*a)) & (4+(3*a))<=(y+(3*b))) | 
         (a<b & (y+(3*b))<=(3+(3*a)) & (4+(3*b))<=(x+(3*a))))) -> 
       requires emp & MayLoop[]
       ensures true & true;
       
         
       a<b & (x+(2*a))<=(2+(2*b)) & (2+b)<=(x+a) & (y+(2*b))<=(2+(2*a)) -> 
       requires emp & Term[64,7]
       ensures true & true;
       
         
       a<b & (a+x)<=(1+b) & (y+b)<=(1+a) & 1<=x -> 
       requires emp & Term[64,5]
       ensures true & true;
       
         
       }
       
     }
     
   1<=y & 1<=x -> 
   case {
     a!=b -> requires emp & Loop{call 14:4}[]
             ensures false & false;
             
               
     b=a -> 
     requires emp & Term[64,4,-1+(0*x)+(1*y)+(0*a)+(0*b)]
     ensures true & true;
     
       
     }
     
   x<=0 & 1<=y -> 
   case {
     a<b -> requires emp & Loop{call 14:4}[]
            ensures false & false;
            
              
     a=b -> 
     requires emp & Term[64,3,-1+(0*x)+(1*y)+(0*a)+(0*b)]
     ensures true & true;
     
       
     b<a -> 
     case {
       (((b<a & x<=0 & (2+a)<=(y+b)) | 
         (x<=0 & 1<=y & (y+b)<=(1+a) & (2+b)<=(x+a)))) & 
       (((b<a & (2+a)<=(y+b) & (x+(2*a))<=(2+(2*b)) & (y+(2*b))<=(2+(2*a))) | 
         (x<=0 & b<a & (3+(2*a))<=(y+(2*b))) | 
         (x<=0 & (2+a)<=(y+b) & (3+(2*b))<=(x+(2*a)) & (y+(2*b))<=(2+(2*a))) | 
         (x<=0 & 1<=y & (2+b)<=(x+a) & (y+b)<=(1+a)))) -> 
       requires emp & MayLoop[]
       ensures true & true;
       
         
       b<a & 1<=y & (x+a)<=(1+b) & (y+b)<=(1+a) -> 
       requires emp & Term[64,6]
       ensures true & true;
       
         
       }
       
     }
     
   }


 */
