struct pair {
  int x;
  int y;
};

int first(struct pair p)
/*@
  requires p::pair<a,b>
  ensures p::pair<a,b> & res = a;
*/
{
  return p.x;
}

int first2(struct pair* p)
/*@
  requires p::pair^<a,b>
  ensures  p::pair^<a,b> & res = a;
*/
{
  return p->x;
}

int first3(struct pair** p)
/*@
  requires p::pair^^<a,b>
  ensures  p::pair^*<a,b> & res = b;
*/
{
  return (*p)->y;
}
