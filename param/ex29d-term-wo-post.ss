
relation R(int x,int y,int a,int b).

void loo (ref int x, ref int y,int a, int b)
  infer [@term]
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
# ex29d.ss --dis-analyse-param

# without post
  infer [@term]
  requires true
  ensures true;

# why is post being inferred by TNT?

Procedure loo: UNKNOWN
 requires true & true
 case {
   y<=0 & x<=0 -> 
   requires emp & Term[64,1]
   ensures true & ((0>=y & 0>=x & y=y' & x=x') | 
                   (0>=y' & 0>=x' & (y+x)>=(2+y'+x')));
   
     
   y<=0 & 1<=x -> 
   case {
     b<=a -> 
     case {
       y<=0 & b<=a & (3+(2*b))<=(x+(2*a)) & 1<=x -> 
       requires emp & MayLoop[]
       ensures true & ((0>=y & 0>=x & y=y' & x=x') | 
                       (0>=y' & 0>=x' & (y+x)>=(2+y'+x')));
       
         
       b=a & x=2 & y<=0 -> 
       requires emp & Term[64,4]
       ensures true & ((0>=y & 0>=x & y=y' & x=x') | 
                       (0>=y' & 0>=x' & (y+x)>=(2+y'+x')));
       
         
       x=1 & b=a & y<=0 -> 
       requires emp & Term[64,2]
       ensures true & ((0>=y & 0>=x & y=y' & x=x') | 
                       (0>=y' & 0>=x' & (y+x)>=(2+y'+x')));
       
         
       }
       
     a<b -> 
     requires emp & MayLoop[]
     ensures true & ((0>=y & 0>=x & y=y' & x=x') | 
                     (0>=y' & 0>=x' & (y+x)>=(2+y'+x')));
     
       
     }
     
   1<=x & 1<=y -> 
   requires emp & MayLoop[]
   ensures true & ((0>=y & 0>=x & y=y' & x=x') | 
                   (0>=y' & 0>=x' & (y+x)>=(2+y'+x')));
   
     
   x<=0 & 1<=y -> 
   case {
     a<=b -> 
     case {
       x<=0 & a<=b & (2+a)<=(y+b) & 1<=y -> 
       requires emp & MayLoop[]
       ensures true & ((0>=y & 0>=x & y=y' & x=x') | 
                       (0>=y' & 0>=x' & (y+x)>=(2+y'+x')));
       
         
       y=1 & a=b & x<=0 -> 
       requires emp & Term[64,3]
       ensures true & ((0>=y & 0>=x & y=y' & x=x') | 
                       (0>=y' & 0>=x' & (y+x)>=(2+y'+x')));
       
         
       }
       
     b<a -> 
     requires emp & MayLoop[]
     ensures true & ((0>=y & 0>=x & y=y' & x=x') | 
                     (0>=y' & 0>=x' & (y+x)>=(2+y'+x')));
     
       
     }
     
   }

 */
