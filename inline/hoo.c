#include "../examples/working/cparser/stdhip.h"

struct pair {
  int x;
  int y;
};

void hoo(struct pair *q)
/*@
 requires q::pair<a,b>
 ensures true;//q::pair<a,b>;
*/
{
  q = malloc(sizeof(struct pair));
}

int main()
/*
 requires true
 ensures true;
*/
{
  return 1;
}

