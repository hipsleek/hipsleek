struct pair {
  int x;
  int y;
};

int foo(struct pair& p)
/*@
  requires p::pair<a,b>
  ensures p=null & res=a+1;
*/
{
  int r = p.x + 1;
  p = NULL;
  return r;
}

int main()
/*@
  requires true
  ensures true;
*/
{
  struct pair p;
  p.x = 1;
  p.y = 1;
  foo(p);
  return 1;
}

