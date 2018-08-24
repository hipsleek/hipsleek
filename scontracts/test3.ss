

int foo1(ref int y)
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
     return foo(y);
  }
}

int foo(ref int y)
  // case {
     //y<=0 ->
     requires emp & Term[y,1]
     ensures true ;
     // 1<=y -> requires emp & Term[1,y]
     //         ensures true;
  // }
{
    return foo1(y);
}
