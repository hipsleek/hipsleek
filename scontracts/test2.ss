
global int y;

/*
 case {
   y<=0 -> requires true ensures res=0;
   y>0  -> requires true ensures res=0;
 }
*/

int foo1(int x, ref int y)
// requires true & Term[y]
 case {
   y<=0 -> requires Term[] ensures res=0;
   y>0  -> requires Term[y]ensures res=0;
 }
 ensures true;
{
  if (y<=0) return 0;
  else {
     y = y-1;
     return foo(x+1,y);
  }
}


int foo(int x,ref int y
   requires true & Term[y]
   ensures true; //?
{
    return foo1(x+1,y);
}
