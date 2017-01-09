int f(int x) 
 infer[@term]
  requires true
  ensures true;
/*
 case {
  x<0 -> requires Term[] ensures res=0;
  x>=0 -> requires Loop ensures false;
}
*/
{ if (x<0) return 0;
  else return f(x-1)+f(x+1);
}

/*
# mult1.ss 

Multiple return LOOP not detected properly.

Got:
f:  case {
  0<=x -> requires emp & MayLoop[]
 ensures emp & true; 
  x<=(0-1) -> requires emp & Term[30,1]
 ensures emp & true; 
  }
Should get:

f:  case {
  0<=x -> requires emp & Loop]
 ensures false; 
  x<=(0-1) -> requires emp & Term[30,1]
 ensures emp & true; 
  }



case x<0:
 x<0 & fpre(x) --> fpost(x) //term

case x>=0 // F(x)
 x>=0 & x1=x-1 & fpre(x) --> fpre(x1)
 x>=0 & x2=x+1 & fpre(x) --> fpre(x2)
 x>=0 & x1=x-1 & x2=x+1 & fpost(x1) & fpost(x2) --> fpost(x)

 F(x) & x1=x-1 & x2=x+1 --> F(x1)
 F(x) & x1=x-1 & x2=x+1 --> F(x2)


 x>=0 & x1=x-1 & x2=x+1 & (x1>=0->false) & (x2>=0->false) --> false


 x>=0 


 x>=0 & x1=x-1 & x2=x-1 & 
    fpost(x1) & fpost(x2)
     --> fpost(x)

 x>=0 & x1=x-1 & x2=x-1 & 
    (x1>=0->false) & (x2>=0->false)  
     --> false

*/

