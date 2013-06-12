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
  requires p::pair*<q> * q::pair<a,b>
  ensures  p::pair*<q> * q::pair<a,b> & res = a;
  //requires p::pair^<a,b>
  //ensures  p::pair^<a,b> & res = a;
*/
{
  return p->x;
}

int first3(struct pair** p)
/*@
  requires p::pair**<q> * q::pair*<r> * r::pair<a,b>
  ensures  p::pair**<q> * q::pair*<r> * r::pair<a,b> & res = a;
  //requires p::pair^^<a,b>
  //ensures  p::pair^^<a,b> & res = a;
*/
{
  return (*p)->x;
}
