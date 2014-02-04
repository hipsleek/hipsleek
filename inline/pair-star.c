// C-program below compile which
// suggest that foo and star_foo are equivalent.
// removing addr-of operator
struct pair {
  int x;
  int y;
};
 
int foo(struct pair* q)
/*@
  requires q::pair<a,b>@L
  ensures res=b;
*/
{
  return q->y;
}

int star_foo(struct pair *q)
/*@
  requires q::pair<a,b>@L
  ensures res=b;
*/
{
  return (*q).y;
}

void main()
{
  struct pair p;
  star_foo(&p);
}
