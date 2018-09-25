
global int y;



/*
Procedure foo1: TRUE
 requires true & true
 case {
   y_21<=0 -> requires emp & Term[40,1]
              ensures true & true;
   1<=y_21 -> requires emp & Term[40,3,0+(0*x)+(2*y_21)]
              ensures true & true;
   }
*/

int foo1(int x)
   // infer [@term]
   // requires true
   // ensures  true ;
  requires true & true
  case {
   y<=0 -> requires emp & Term
           ensures true & true;
   1<=y -> requires emp & Term[y+y]
           ensures true & true;
  }
{
  if (y<=0) return 0;
  else {
     y = y-1;
     return foo(x+1);
  }
}


/*
 case {
   1<=y_22 -> requires emp & Term[40,3,1+(0*x)+(2*y_22)]
              ensures true & true;
   y_22<=0 -> requires emp & Term[40,2]
              ensures true & true;
   }
*/
int foo(int x)
    // infer [@term]
    //  requires true
    //  ensures  true;
   requires true & true
   case {
     1<=y -> requires emp & Term[1+y+y]
             ensures true & true;
     y<=0 -> requires emp & Term
             ensures true & true;
   }
{
    return foo1(x+1);
}
