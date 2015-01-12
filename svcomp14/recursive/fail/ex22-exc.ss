data cell {
  int val;
}

int exc()
  requires true
  ensures true & flow __Exc;


bool rand() 
  requires true
  ensures true & (!res | res);

int main()
  requires true
  ensures true & flow __Exc or true & flow __norm;
{
  int r = 1;
  if (rand()) r=exc();
  // dprint;
  return r;
}



/*
# ex22c-null-err.ss

Expecting failure but why is main
verified successfully? Unsound here.

Why is dprint not printed?
Please fix dprint first.

Checking procedure null_err$... 
Procedure null_err$ SUCCESS.

Checking procedure main$... 
Procedure main$ SUCCESS.
Stop Omega... 39 invocations 


*/
