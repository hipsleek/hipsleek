struct pair {
  int x;
  int y;
};

struct pair q;

int global_struct()
/*@
  requires true
  ensures  res=1;
*/
{
  q.x = 1;
  q.y = 3;
  return q.x;
}


int local_struct()
/*@
  requires true
  ensures  res=1;
*/
{
  struct pair v;
  v.x = 1;
  v.y = 2;
  return v.x;
}
