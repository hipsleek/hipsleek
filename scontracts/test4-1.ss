
global int y;

int foo1()
  //infer [@term]
  case {
   y<=0 -> requires emp & Term
           ensures true;
   1<=y -> requires emp & Term[y,0]
           ensures true ;
  }
{
  if (y<=0) return 0;
  else {
     y = y-1;
     return foo();
  }
}

void goo()
  requires true & Term
  ensures  true;

int foo()
   //infer [@term]
   case {
     y<=0 -> requires emp & Term
             ensures true ;
     1<=y -> requires emp & Term[y,1]
             ensures true;
   }
{
    goo(); //???
    return foo1();
}
