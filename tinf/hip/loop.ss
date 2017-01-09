/* bubble sort */

void loop()
 requires Loop
 ensures false;

void foo(int i)
  infer [@term]
  requires true  ensures true;
{
  if (i==0) return;
  else {
    loop();
  };
}

/*
# loop.ss

Need to pick up 
   ctx & false --> Loop

Otherwise, case-split will have missing
case, as below.

foo:  case {
  i=0 -> requires emp & Term[30,1]
 ensures emp & true; 
  }

*/
