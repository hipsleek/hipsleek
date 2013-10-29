// pass-by-value
//#include <stdlib.h>

data pair {
  int x;
  int y;
}

data pair_star{
  pair deref;
}

data int_star{
  int deref;
}

void hoo(pair q_star)
 requires q_star::pair<a,b>
 ensures q_star::pair<a,b>;
{
  pair_star q = new pair_star(q_star);
  q.deref = new pair(0,0);
}

void hoo2(pair q_star)
 requires q_star::pair<a,b>
 ensures q_star::pair<a,b>;
{
  q_star = new pair(0,0);
}

int main() 
 requires true
 ensures res=1;
{
  return 1;
}

