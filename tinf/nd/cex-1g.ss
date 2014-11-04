int g(int x) 
  infer [@term]
  requires true
  ensures true;
{
   return x+10;
}

void hhh(int x) 
  infer [@term]  requires true ensures true;
{
   if (x < 0) return;
   else if (x<100)
     hhh(g(x));
   else if (x<109)  // if change to 110, it terminates
     return;
   else hhh(x);
}


void main ()
  infer [@term]
  requires true
  ensures true;
{
  int x;
  x = 2;
  hhh(x);
}

/*
  expects TERM but returns MAYLOOP
*/
