

int foo1(ref int y)
  //infer [@term]
  case {
   y<=0 -> requires emp & Term
           ensures true;
   1<=y -> requires emp & Term[y,0]
           ensures true ;
  }
{
  int z = y;
  if (z<=0) return 0;
  else {
     z = z-1;
     return foo(z);
  }
}

void goo()
  requires true & Term
  ensures  true;

int foo(ref int y)
   //infer [@term]
   case {
     y<=0 -> requires emp & Term
             ensures true ;
     1<=y -> requires emp & Term[y,1]
             ensures true;
   }
{
    goo(); //???
    return foo1(y);
}
