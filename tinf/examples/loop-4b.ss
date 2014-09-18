void loop ()
  requires Loop
  ensures false;

void f (int x)
  infer [@term]
  requires true
  ensures true;
{
    loop();
    f(x + 1);
}

/*
# loop-4b.ss

Missing cases for pre of f & post of f.

 termAssume x'=x & fpre_0(x) --> Loop.

*/
