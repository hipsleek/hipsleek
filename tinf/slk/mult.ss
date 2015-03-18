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

int f2(int x, int y) 
 infer[@term]
  requires true
  ensures true;
/*
  case {
  x<0 -> requires Term[] ensures res=0;
  x>=0 -> 
   case {
    y<0 -> requires Term[?] ensures true;
    y>=0 -> requires Loop ensures false;
   }
 }
*/
{ if (x<0) return 0;
  else return f2(x+y,y);
}

/*
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
