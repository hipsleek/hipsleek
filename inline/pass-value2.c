// pass-by-value

struct pair {
  int x;
  int y;
};

int goo(struct pair* q)
// pass by value
/*@
  requires q::pair<a,b>
  ensures q::pair<a,b> & res=a;
*/
{
  return q->x;
}

int goo2(struct pair *q)
// pass by ptr
/*@
  requires q::pair<a,b>
  ensures q::pair<a,b> & res=a;
*/
{
  return (*q).x;
}

/*

 *q --> ptr_q

int goo_ptr(pair ptr_q)
  requires ptr_q::pair<a,b>
  ensures ptr_q::pair<a,b> & res=a;
{
  return ptr_q.x;
}

 goo(q) ==> goo_ptr(*q)

*/

void main ()
/*@
  requires true
  ensures true;
*/
{
  return;
}

