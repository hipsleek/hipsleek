/*
while(x>=0) {
  if b {
      x=x-1;
    };
  b=not(b);
}
*/

int cycle(int i) 
  requires 0<=i<=5 
  ensures (i=0 & res=5 | i>0 & res=i-1);
{
  if (i==0) return 5;
  else return i-1;
}

void foo(int b,int x)
 infer [@term]
 requires 0<=b<=5
  ensures true;
{ 
  if (x>=0) {
    if (b==0) x=x-1;
    b=cycle(b);
    foo(b,x);
  }
}

/*
# ex41b.ss


# What is t_foo_20_1??

Procedure foo: TRUE
 requires emp & 0<=b & b<=5
 case {
   x<=(0-1) -> requires emp & Term[35,1]
               ensures true & true;
               
                 
   1<=b & 0<=x -> requires emp & Term[35,2,0+(1*b)+(6*x)]
                  ensures true & true;
                  
                    
   b<=0 & 0<=x -> 
   requires emp & Term[35,2,0+(t_foo_20_1*b)+(6*x)]
   ensures true & true;
   
     
   }



 */
