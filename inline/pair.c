struct pair {
	int x;
	int y;
};

int main() 
/*@
  requires true
  ensures res=2;
*/
{
  struct pair p;
  p.x = 1;
  struct pair* pp;
  pp = &p;
  pp->x = pp->x +1;
  return pp->x;

}
