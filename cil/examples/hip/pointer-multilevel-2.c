struct node {
  int x;
  int y;
};

int foo1 (struct node* p)
/*@
  requires p::node^<x, _>
  ensures p::node^<x-1, _>;
*/
{
  (*p).x = (*p).x - 1;
  return 0;
}


int foo2 (struct node** p)
/*@
  requires p::node^^<x, _>
  ensures p::node^^<x-1, _>;
*/
{
  (**p).x = (**p).x - 1;
  return 0;
}

int foo3 (struct node*** p)
/*@
  requires p::node^^^<x, _>
  ensures p::node^^^<x-1, _>;
*/
{
  (***p).x = (***p).x - 1;
  return 0;
}
