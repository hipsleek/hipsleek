data PACKET{
  lbit lock;
  int count;
  int data;
}

global PACKET p;

inv(p,M) == p.count::int<X> * p.data::int<_>
  * ((X=0) or (p::LOCK(X/M)<M> & X>=1));

void initialize()
requires true & MUST ={} & MAY ={}
ensures p::LOCK<M> & MUST ={} & MAY ={};
{
  //{true & MUST ={} & MAY ={}}
  p = new PACKET(0,_);
  //{p.lock::lbit<_> * p.count::int<0> * p.data::int<_> & MUST ={} & MAY ={}}
  init(p) with inv(p,M);
  //{p::LOCK<M> * p.count::int<0> * p.data::int<_> & MUST ={p} & MAY ={p}}
  release(p);
  //{p::LOCK<M> & MUST ={} & MAY ={}}
}

void thread()
  requires p::LOCK(1/M)<M> & MUST ={} & MAY ={}
  ensures true & MUST ={} & MAY ={};
{
  //{p::LOCK(1/M)<M> & MUST ={} & MAY ={}}
  acquire(p);
  //{p.count::int<X> * p.data::int<_> * p::LOCK((X + 1)/M)<M> & 0≤X<M & MUST={p} & MAY ={p}}
  // . . . processing data . . .
  p.count++;
  //{p.count::int<X> * p.data::int<_> * p::LOCK(X/M)<M> & 1≤X≤M & MUST ={p} & MAY ={p}}
  if (p.count == M){
    //{p.count::int<X> * p.data::int<_> * p::LOCK<M> & MUST ={p} & MAY ={p}}
    // . . . Finalizing data . . .
    finalize(l);
    //{p.count::int<X> * p.data::int<_> * p.lock::lbit<> & MUST ={} & MAY ={}}
    delete(p);
  }else{
    //{p.count::int<X> * p.data::int<_> * p::LOCK(X/M)<M> & 1≤X<M & MUST ={p} & MAY ={p}}
    release(p);
  }
  //{true ∧ MUST ={} ∧ MAY ={}}
}
