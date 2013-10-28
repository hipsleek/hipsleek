data pair {
	int x;
	int y;
}
data pair_star {
  pair deref;
}

int main() 
  requires true
  ensures res=2;
{
  pair addr_p = new pair(0,0); //stack allocate
  addr_p.x = 1;
  pair_star addr_pp = new pair_star(null); // stack allocate
  addr_pp.deref = addr_p;
  addr_pp.deref.x = addr_pp.deref.x +1;
  pair_star ppp;
  ppp = addr_pp;
  return ppp.deref.x;
}
/*
  struct pair p  ==> pair addr_p=new pair(0,0) //stack allocat 
  & p     ==> addr_p
  p.field ==> addr_p.field
  p       ==> ?
*/

