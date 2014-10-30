void loop()
  requires Loop
  ensures false;

int g(int x) 
  infer [@term]
  requires true
  ensures true;
{
   return x+1;
}

void h(int x) 
  infer [@term]
  requires true
  ensures true;
{
   if (x < 0) return;
   else if (x<10)
      h(g(x));
   else h(x);
}


void main ()
  infer [@term]
  requires true
  ensures true;
{
  int x;
  x = 2;
  h(x);
}
