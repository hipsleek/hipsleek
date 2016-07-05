void acquire()
  requires true
  ensures false;

bool[] update___1d(bool v, bool[] a, int i)
	requires [ahalb,ahaub] domb(a,ahalb,ahaub) & ahalb <= i & i <= ahaub
	ensures domb(res,ahalb,ahaub) & update_array_1d_b(a,res,v,i);
