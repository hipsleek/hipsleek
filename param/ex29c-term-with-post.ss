
relation R(int x,int y,int a,int b).

void loo (ref int x, ref int y,int a, int b)
  infer [@term]
  requires true
  ensures y<=0 & x<=0 & y=y' & x=x' | y'<=0 & x'<=0 & y+x>=2+y'+x';
{

  if (x>0 || y>0) {
    //dprint;
    x = x+a-b-1;
    y = y+b-a-1;
    loo(x,y,a,b);
  };
}

/*
# ex29c.ss --dis-analyse-param

# why did adding valid postcond affect this @term result?

# with post
  infer [@term]
  requires true
  ensures y<=0 & x<=0 & y=y' & x=x' | y'<=0 & x'<=0 & y+x>=2+y'+x';

Termination Inference Result:
Procedure loo: UNKNOWN
 requires true & true
 case {
   y<=0 & x<=0 -> 
   requires emp & Term[64,1]
   ensures emp & (((0>=x' & x>=x' & 0>=y' & (y+x)>=(2+x'+y')) | 
                   (0>=x' & y>=y'))) & 
                 (((y<=0 & x<=0 & y=y' & x=x') | 
                   (y'<=0 & x'<=0 & (x'+2+y')<=(x+y))));
   
     
   y<=0 & 1<=x -> 
   case {
     ((a<b & (y+a)<=b) | (b<=a & b<(y+a))) -> 
     requires emp & MayLoop[]
     ensures emp & (((0>=x' & x>=x' & 0>=y' & (y+x)>=(2+x'+y')) | 
                     (0>=x' & y>=y'))) & 
                   (((y<=0 & x<=0 & y=y' & x=x') | 
                     (y'<=0 & x'<=0 & (x'+2+y')<=(x+y))));
     
       
     b<=a & (y+a)<=b -> 
     case {
       b<=a & (y+a)<=b & (5+(4*b))<=(x+(4*a)) & 1<=x -> 
       requires emp & MayLoop[]
       ensures emp & (((0>=x' & x>=x' & 0>=y' & (y+x)>=(2+x'+y')) | 
                       (0>=x' & y>=y'))) & 
                     (((y<=0 & x<=0 & y=y' & x=x') | 
                       (y'<=0 & x'<=0 & (x'+2+y')<=(x+y))));
       
         
       x=4 & b=a & y<=0 -> 
       requires emp & Term[64,5]
       ensures emp & (((0>=x' & x>=x' & 0>=y' & (y+x)>=(2+x'+y')) | 
                       (0>=x' & y>=y'))) & 
                     (((y<=0 & x<=0 & y=y' & x=x') | 
                       (y'<=0 & x'<=0 & (x'+2+y')<=(x+y))));
       
         
       x=3 & b=a & y<=0 -> 
       requires emp & Term[64,4]
       ensures emp & (((0>=x' & x>=x' & 0>=y' & (y+x)>=(2+x'+y')) | 
                       (0>=x' & y>=y'))) & 
                     (((y<=0 & x<=0 & y=y' & x=x') | 
                       (y'<=0 & x'<=0 & (x'+2+y')<=(x+y))));
       
         
       x=2 & b=a & y<=0 -> 
       requires emp & Term[64,3]
       ensures emp & (((0>=x' & x>=x' & 0>=y' & (y+x)>=(2+x'+y')) | 
                       (0>=x' & y>=y'))) & 
                     (((y<=0 & x<=0 & y=y' & x=x') | 
                       (y'<=0 & x'<=0 & (x'+2+y')<=(x+y))));
       
         
       b<=a & (x+a)<=(1+b) -> 
       requires emp & Term[64,2]
       ensures emp & (((0>=x' & x>=x' & 0>=y' & (y+x)>=(2+x'+y')) | 
                       (0>=x' & y>=y'))) & 
                     (((y<=0 & x<=0 & y=y' & x=x') | 
                       (y'<=0 & x'<=0 & (x'+2+y')<=(x+y))));
       
         
       }


 */
