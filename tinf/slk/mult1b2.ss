int f2(int x, int y) 
 infer[@term]
//requires true ensures res=0;
// mult1b.ss (new syntax)
  case {
  x<0 -> requires Term[] ensures res=0;
  x>=0 -> 
   case {
    y<0 -> requires true // Term[?] 
           ensures true;
    y>=0 -> requires true ensures true;
   }
}
{ if (x<0) return 0;
  else return f2(x+y,y);
}

/*
# mult1b2.ss

Loop not detected when post is not given false

Got:
f2:  case {
  x<0 -> requires emp & Term[29]
 ensures emp & res=0; 
  0<=x -> case {
           y<0 -> requires emp & MayLoop[]
 ensures emp & true; 
           0<=y -> requires emp & MayLoop[]
 ensures emp & true; 
           }
  
  }

Expects:
f2:  case {
  0<=x -> case {
           (0+(0*x)+(1*
           y))>=0 -> requires emp & Loop[]
 ensures false & false; 
           (0+(0*x)+(1*y))<0 -> requires emp & Term[29,4,0+(1*x)+(0*
           y)]
 ensures emp & true; 
           }
  
  x<=(0-1) -> requires emp & Term[29,1]
 ensures emp & true; 
  }



case x<0
 x<0 & fpre(x,y) --> fpost(x,y)

case x>=0:
 x>=0 & x1=x+y & fpre(x,y) --> fpre(x1,y)
 x>=0 & x1=x+y & fpre(x,y) & fpost(x1,y) --> fpost(x,y)  // MayLoop

case x>=0, y<0
 y<0 & x>=0 & x1=x+y & fpre(x,y) & y2=y+1--> fpre(x1,y2) // term
 //y<0 & x>=0 & x1=x+y & fpre(x,y) & fpost(x1,y) --> fpost(x,y)

case x>=0, y>=0
 //y>=0 & x>=0 & x1=x+y & fpre(x,y) --> fpre(x1,y)
 y>=0 & x>=0 & x1=x+y & fpre(x,y) & fpost(x1,y) --> fpost(x,y) // false


 Case x>=0  (F(x,y) == x>=0)
   x>=0 & x1=x+y & fpost(x1,y) --> fpost(x,y)  // MayLoop
 
   F(x,y) & x1=x+y --> F(x1,y)

 Case x>=0 & y>=0  (F(x,y) == x>=0 & y>=0 )
   F(x,y) & x1=x+y --> F(x1,y)

 
 
*/
