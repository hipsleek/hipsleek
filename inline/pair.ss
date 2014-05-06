data pair {
	int x;
	int y;
}

int main() 
  requires true
  ensures res=2;
{
  pair addr_p = new pair(0,0); //stack allocate
  addr_p.x = 1;
  pair pp;
  pp = addr_p;
  pp.x = pp.x +1;
  return pp.x;
}
/*
  struct pair p  ==> pair addr_p=new pair(0,0) //stack allocat 
  & p     ==> addr_p
  p.field ==> addr_p.field
  p       ==> ?
*/

