

data TaylorSeriesIte
{

}
 int TaylorSeriesIte_power(int a, int b)
{
  int p = 1;
  
  int i = 1;
  while (i <= b) {
    p *= a;
    i++;
  }
  
  return p;
}

int TaylorSeriesIte_fact(int n)
{
  int p = 1;
  
  int i = 1;
  while (i <= n) {
    p *= i;
    i++;
  }
  
  return p;
}

int TaylorSeriesIte_sin(int x, int n)
{
  int s = x;
  
  int i = 3;
  while (i <= n) {
    s += TaylorSeriesIte_power(-1, i / 2) * TaylorSeriesIte_power(x, i) / TaylorSeriesIte_fact(i);
    i += 2;
  }
  
  return s;
}

int TaylorSeriesIte_cos(int x, int n)
{
  int s = 1;
  
  int i = 2;
  while (i <= n) {
    s += TaylorSeriesIte_power(-1, i / 2) * TaylorSeriesIte_power(x, i) / TaylorSeriesIte_fact(i);
    i += 2;
  }
  
  return s;
}

int TaylorSeriesIte_exp(int x, int n)
{
  int s = 0;
  
  int i = 0;
  while (i <= n) {
    s += TaylorSeriesIte_power(x, i) / TaylorSeriesIte_fact(i);
    i++;
  }
  
  return s;
}

void TaylorSeriesIte_main(String[] args)
{
  
  int i = 0;
  while (i < args.length) {
    if (i % 2 == 0)
      TaylorSeriesIte_sin(args.length, i);
    else if (i % 3 == 0)
      TaylorSeriesIte_cos(args.length, i);
    else if (i % 5 == 0)
      TaylorSeriesIte_exp(args.length, i);
    else
      
      int j = 0;
      while (j < 100) {
        ;
        j++;
      }
      
    i++;
  }
  
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;