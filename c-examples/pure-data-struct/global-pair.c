struct pair {
  int x;
  int y;
};

struct pair q;
int a;

/*@
relation A(int x, pair y, pair z).
relation B(int x).
*/

int global_struct()
/*@
  infer [A]
  requires q::pair<_,_>
  ensures  q'::pair<1,3> & A(res, q, q');
*/
{
  a = 3;
  q.x = 1;
  q.y = 3;
  return q.x;
}


int local_struct()
/*@
  infer [B]
  requires true
  ensures  B(res);
*/
{
  struct pair v;
  v.x = 1;
  v.y = 2;
  return v.x;
}
