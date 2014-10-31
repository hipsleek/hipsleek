void loop()
  requires Loop
  ensures false;

bool nondet()
  requires Term
  ensures true;
  
void f(int x)
  infer [@term]
  requires true
  ensures true;
{
  if (x < 0) return;
  else {
    bool b = nondet();
    if (b)
      /* return; */
      f(x + 1);
    else
      /* f(x + 2); */
      return;
      /* loop(); */
  }
}


void g(int x) 
//infer [@term]  requires true ensures true;
{
   if (x > 0)
      f(x);
}

void main ()
  infer [@term]
  requires true
  ensures true;
{
  int x;
  g(x);
}
