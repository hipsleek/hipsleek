void loop(ref int x, ref int y)
 infer [@term] 
 requires true
  ensures true;
{ if (x>y) {
    y=x+y;
    x=x+1;
    loop(x,y);
  }
}

/*
i-sim2-loop.ss

Why so complex and with some MayLoop?

loop:  requires true & truecase {
                      x<=y -> requires emp & Term[66,1]
     ensures true & true;
                      
                      y<x & x<=0 & y<=(0-2) -> requires emp & Loop
                      { 8:4}[]
     ensures false & false; 
                      y<=(0-2) & 
                      1<=x -> case {
                               ((3<=x & x<=((0-y)-2)) | (x=2 & y<=(0-
                               2))) -> requires emp & MayLoop[]
     ensures true & true;
                               
                               ((0-x)-1)<=y & y<=(0-2) & 
                               3<=x -> requires emp & Term[66,4]
     ensures true & true;
                               
                               x=1 & y<=(0-3) -> requires emp & Loop
                               { 8:4}[]
     ensures false & false; 
                               x=1 & y=0-
                               2 -> requires emp & Term[66,3]
     ensures true & true;
                               
                               }
                      
                      (0-1)<=y & 
                      y<x -> requires emp & Term[66,2]
     ensures true & true;
                      
                      }

*/
