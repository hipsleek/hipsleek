data PACKET{
  lbit lock;
  int count;
  int data;
}

global PACKET p;

inv<p,M> == p::PACKET<_,count,data> * count::int<X> * data::int<_>
  * ((X=0) or (p::LOCK(X/M)<M> & X>=1));

void initialize()
requires true & MUST ={} & MAY ={}
ensures p::LOCK<M> & MUST ={} & MAY ={};
{
  //{true & MUST ={} & MAY ={}}
  p = new PACKET(0,_);
  //{p::PACKET<lock,count,data> * lock::lbit<_> * count::int<0> * data::int<_> & MUST ={} & MAY ={}}
  init(p,M);
  //{p::LOCK<M> * p::PACKET<_,count,data> * count::int<0> * data::int<_> & MUST ={p} & MAY ={p}}
  release(p);
  //{p::LOCK<M> & MUST ={} & MAY ={}}
}

void thread()
  requires p::LOCK(1/M)<M> & MUST ={} & MAY ={}
  ensures true & MUST ={} & MAY ={};
{
  //{p::LOCK(1/M)<M> & MUST ={} & MAY ={}}
  acquire(p);
  //{p::PACKET<_,count,data> * count::int<X> * data::int<_> * p::LOCK((X + 1)/M)<M> & 0≤X<M & MUST={p} & MAY ={p}}
  // . . . processing data . . .
  p.count++;
  //{p::PACKET<_,count,data> * count::int<X> * data::int<_> * p::LOCK(X/M)<M> & 1≤X≤M & MUST ={p} & MAY ={p}}
  if (p.count == M){
    //{p::PACKET<_,count,data> *  count::int<X> * data::int<_> * p::LOCK<M> & MUST ={p} & MAY ={p}}
    // . . . Finalizing data . . .
    finalize(l);
    //{p::PACKET<lock,count,data> * count::int<X> * data::int<_> * lock::lbit<> & MUST ={} & MAY ={}}
    delete(p);
  }else{
    //{p::PACKET<_,count,data> * count::int<X> * data::int<_> * p::LOCK(X/M)<M> & 1≤X<M & MUST ={p} & MAY ={p}}
    release(p);
  }
  //{true ∧ MUST ={} ∧ MAY ={}}
}
