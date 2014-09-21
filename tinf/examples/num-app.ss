

/* append two singly linked lists */

void append2(int x, int y)
  infer [@term]
  requires x>0 & y>=0 
  ensures true ;
{    
	if (x == 1) 
          return;
	else
           append2(x-1, y);
}

/*
# num-app.ss

  infer [@term]
  requires x>0 & y>=0 
  ensures true ;

good case analysis here;
similar but seems better than ll-app.ss. Why?

append2:  requires emp & 0<x & 0<=y
  case {
     x=1 & 0<=y -> 
       requires emp & Term[8,1]
       ensures emp & true; 
     2<=x & 0<=y -> 
       requires emp & Term[8,2,-1+(1*x)+(0*y)]
       ensures emp & true; 
     }

 */




