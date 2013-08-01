struct pair {
  int x;
  int y;
};

struct node {
  struct pair a;
  int b;
};

struct node p = {.a.y = 2};

struct node q = {{1, 2}, 3};

int foo()
/*@
  requires q::node<n,_> * n::pair<_, _>
  ensures  q'::node<n,_> * n::pair<1,2> & res=1 & q'=q;
*/
{
  q.a.x = 1;
  q.a.y = 2;
  return q.a.x;
}
