

void loop()
 requires Loop
  ensures false;


int non_det()
 requires true & Term[]
 ensures true;


void loop(int x, int y)
 infer [@term]
 requires true
 ensures true;
{
  int k = non_det();
  if (x>=0 
      && (k>0)) {
    x = x + y;
    loop(x, y);
 }
}

/*
# nd3a.ss

Why did it not complain about two loop methods
with the same name?

Result is unexpected..

*/
