// C-program below compile which
// suggest that foo and star_foo are equivalent.
// removing addr-of operator
struct pair {
  int x;
  int y;
};
 
int foo(struct pair* q)
/*@
  requires q::pair<a,b>
  ensures q::pair<a,b> & res=b;
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
  foo(&p);
}

/*
{local: pair p
pair p = new pair(0, 0);
{(76, ):foo(p);
(77, ):return }}
}
*/
