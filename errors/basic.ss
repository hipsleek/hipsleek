
int f(int x, int y)
 case {
  x>1 ->
  case {
   y>0 -> ensures true & flow __Error;
   y<=0 -> //ensures true & flow __flow;
     ensures res=2 or true & flow __Error;
  }
  x<=1 -> ensures res=5;
 }
 { 
   if (x>1) {
     if (y>0) { error();
       /* state 1 */ return 1;
     } else {
       if (randBool()) {
       /* state 2 */ return 2;
       } else { error(); 
       /* state 3 */ return 3;
       };
     }
   } else if (x>2) {
     /* state 4 */ return 4; /* dead code */
   } else {
     /* state 5 */ return 5;
   }
 }

void error() 
  requires true
  ensures true & flow __Error;

bool randBool() 
  requires true
  ensures true;
