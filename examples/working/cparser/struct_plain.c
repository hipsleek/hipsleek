struct pair {
  int x;
  int y;
};

struct pair q;

int global_struct()
/*@
  requires q::pair<_,_>
  ensures  q'::pair<1,3> & res=1 & q'=q;
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
