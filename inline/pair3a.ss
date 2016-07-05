data pair {
	int x;
	int y;
}
data pair_star {
  pair deref;
}
data pair_star_star {
  pair_star deref;
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
  pair_star_star addr_ppp = new pair_star_star(null);
  addr_ppp.deref = addr_pp;
  return addr_ppp.deref.deref.x;
}
/*
  struct pair p  ==> pair addr_p=new pair(0,0) //stack allocat 
  & p     ==> addr_p
  p.field ==> addr_p.field
  p       ==> ?
*/

