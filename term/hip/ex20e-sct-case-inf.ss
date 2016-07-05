
int randI() 
  requires Term[]
  ensures true;


void loo (ref int xxx, ref int y,int a, int b)
/*
 case {
   x>0 -> 
    case {
     a=b -> requires Term[x]
       ensures true;
     a!=b -> requires MayLoop
             ensures true;
     }
   x<=0 ->
     requires Term[] ensures true;
 }
*/
 infer [@term]
 requires true
  ensures true;
{
  if (xxx>0) {
    xxx = xxx+a-b-1;
    y = y+b-a-1;
    loo(xxx,y,a,b);
  };
}

/*
# ex20e.ss

Base/Rec Case Splitting:
[	loo: [[2] xxx<=0@B,[3] a<=b & 1<=xxx@R,[4] b<a & 1<=xxx@R]
]

# is this result correct?
# need to improve printing

Termination Inference Result:
Procedure loo: FALSE - Counterexample:  {call 28:4}
 requires true & true
 case {
   x<=0 -> 
   requires emp & Term[63,1]
   ensures true & ((0>=x & 
   x=x' & 
   y=y') | 
   (0>=x' & 
   (x+
   y'+
   (2*
   a))>=(x'+
   y+
   (2*
   b)) & 
   (x'+
   b)>=a & 
   (x+
   y)>=(2+
   x'+
   y')));
   
     
   a<=b & 1<=x -> 
   requires emp & Term[63,2,-1+(1*x)+(0*y)+(0*a)+(0*b)]
   ensures true & ((0>=x & 
   x=x' & 
   y=y') | 
   (0>=x' & 
   (x+
   y'+
   (2*
   a))>=(x'+
   y+
   (2*
   b)) & 
   (x'+
   b)>=a & 
   (x+
   y)>=(2+
   x'+
   y')));
   
     
   b<a & 1<=x -> requires emp & Loop{call 28:4}[]
                 ensures false & false;
                 
                   
   }

 */
