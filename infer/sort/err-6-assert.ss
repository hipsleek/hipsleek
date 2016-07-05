/* selection sort */

data node {
	int val; 
	node next; 
}

class e1 extends __Exc {}

void bindex(node x, node y)
  requires x::node<a,b> 
  ensures  x::node<_,b> & flow e1 ;
{
  //int r=2;
  {
    int r=3;
    assert r'=3;
    assert rr'=1;
    raise new e1();
    dprint;
    assert r'=4 & flow e1;
  }
  dprint;
}

