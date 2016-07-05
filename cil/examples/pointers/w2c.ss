class rExp extends __Exc {
   int val;
}

int foo(int N) 
 requires N>=0
 ensures true;
{
 int i = 0;
 try {
  loop();
 } catch (rExp ot) {
   return ot.val;
 };
}

void loop( )
  requires true
  ensures eres::rExp<_> & flow rExp;
 {
    int i;
    i = 2;
    raise new rExp(i);
 }


