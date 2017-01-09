int f(int x) 
{ 
  if (x<=0) return 0; 
  else return g(x) + g(x+1); 
}

int g(int x) 
{ 
  if (x<=0) return 0; 
  else return f(x-1) + f(x-2);
}

int main()
{
  g(2);
}
