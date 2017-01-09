void loop ()
  requires Loop
  ensures true;

void f (int x)
  infer [@term]
  requires true
  ensures true;
{
    loop();
    f(x + 1);
}
/*
# loop-4a.ss

#loop-4b.ss should also generate:
  false --> fpost_1122(x
  false --> fpre_0(v_int_11_1124')

Below is correct for loop-4a.ss

termAssume x'=x & fpost_1122(1+x') --> fpost_1122(x).

 termAssume x'=x & v_int_11_1124'=1+
x' & fpre_0(x) --> fpre_0(v_int_11_1124').

 termAssume x'=x & fpre_0(x) --> Loop.

*/
