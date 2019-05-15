data int_sec {
  int val;
  int sec;
}
data bool_sec {
  bool val;
  int  sec;
}

int LUB(int x, int y)
  requires true
  ensures  res=max(x,y);

data node {
  int_sec  v;
  node_sec n;
}
data node_sec {
  node val;
  int  sec;
}

int_sec _subS(int_sec x, int_sec y)
  requires x::int_sec<vx,sx> * y::int_sec<vy,sy>
  ensures  (exists smax:res::int_sec<vx-vy, sres> & sres<=smax & smax=max(sx,sy));
{
  int vres = x.val - y.val;
  int vsec = LUB(x.sec, y.sec);
  return new int_sec(vres, vsec);
}

pred secret_ll<n> == self::node_sec<self_val,self_sec> * n::int_sec<n_val,n_sec> & self_val=null & n_val=0
                     & self_sec<=1
                  or self::node_sec<self_val,self_sec> * n::int_sec<n_val,_> * n1::int_sec<n1_val,_>
                     * self_val::node<_,q> * q::secret_ll<n1> & n1_val>0 & n1_val=n_val-1 & self_sec<=1;

pred public_ll<n> == self::node_sec<self_val,self_sec> * n::int_sec<n_val,n_sec> & self_val=null & n_val=0
                     & self_sec<=0
                  or self::node_sec<self_val,self_sec> * n::int_sec<n_val,_> * n1::int_sec<n1_val,_>
                     * self_val::node<_,q> * q::public_ll<n1> & n1_val>0 & n1_val=n_val-1 & self_sec<=0;

node_sec id(node_sec p)
  requires p::secret_ll<n> * n::int_sec<n_val,_> & n_val > 0
  ensures  res::node_sec<_,p_sec> & p_sec <= 1;
{
  return p;
}

node_sec id_succ(node_sec p)
  requires p::public_ll<n>
  ensures  res::secret_ll<n>;
{
  return p;
}

node_sec id_fail(node_sec p)
  requires p::public_ll<n>
  ensures  res::secret_ll<n>;
{
  return p;
}

node_sec sec(node_sec p)
  requires p::public_ll<n>
  ensures  res::secret_ll<n>;
{
  if(p.val == null) {
    return p;
  } else {
    p.sec = LUB(p.sec,1);
    p.val.n = sec(p.val.n);
    return p;
  }
}

node_sec pub(node_sec p)
  requires p::secret_ll<n>
  ensures  res::public_ll<n>;
{
  if(p.val == null) {
    return p;
  } else {
    p.sec = LUB(p.sec,0);
    p.val.n = sec(p.val.n);
    return p;
  }
}
