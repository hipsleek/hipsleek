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

/*

{local: pair p,pair pp
pair p = new pair()
pair pp
{member access p~~>x = 1
pp = p
member access pp~~>x = (int)member access pp~~>x + 1
(113, ):return member access pp~~>x}}
}

# shd have a free p at the end ..

*/
