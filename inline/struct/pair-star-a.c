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


void main()
{
  struct pair p;
  struct pair* pp = &p;
  foo(pp);
}

/*
{local: pair p,pair pp
pair p = new pair(0, 0);
pair pp;
{pp = p;
(74, ):foo(pp);
(75, ):return }}
}
*/
