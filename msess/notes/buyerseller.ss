int get_id()
  requires true
  ensures res>=1;

int get_budget()
  requires true
  ensures res>=0;

int get_price(int id)
  requires id>=1
  ensures res>0;

Addr get_addrs()
  requires true
  ensures res::Addr<_>;

DDate get_date(Addr a, int prod_id)
  requires a::Addr<_> & prod_id >=1
  ensures  a::Addr<_> * res::DDate<_,_,_>;

/* Channel start_shipper() */
/*   requires true */
/*   ensures  res::Chan{@S GSb<>}<>; */

/* void stop_shipper(Channel c) */
/*   requires c::Chan{emp}<> */
/*   ensures  true; */
