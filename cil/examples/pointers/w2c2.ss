class rExp extends __Exc {
}

int foo(int N) 
 requires N>=0
 ensures true;
{
 int i = 0;
 try {
  loop();
 } catch (rExp ot) {
   return 1;
 };
}

void loop( )
  requires true
  ensures eres::rExp<> & flow rExp;
 {
    int i;
    i = 2;
    raise new rExp();
 }


