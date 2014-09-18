void loop ()
  requires Loop
  ensures false;

void f (int x)
  infer [@term]
  requires true
  ensures x>1234;
{
    loop();
    f(x+222);
}

/*
# loop-4b.ss

What happen to the other two cases?
Where is the false pre-state..

Missing cases for pre of f & post of f.

 termAssume x'=x & fpre_0(x) --> Loop.


*/
