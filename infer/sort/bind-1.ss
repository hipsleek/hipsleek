/* selection sort */

data node {
	int val; 
	node next; 
}

class e1 extends __Exc {}

node bindex(node x, node y)
  requires x::node<a,b> 
  ensures  x::node<_,b> & flow e1 ;
{
  //dprint;
  bind x to (xv,xn) in
  {
    //dprint;
    {
    int r=2;
    assert r'=2;
    xv=r;
    //dprint;
    raise new e1();
    xv=3;
    }
  }
  assert xx=2; // need msg for empty context
  dprint;
}

