/* singly linked lists */

/* representation of a node */

data node{
	int val; 
	node next;	
}

ll<R> == R = {}
	or self::node<_@L,p> * p::ll<Rp> & R = union(Rp,{self})
	inv true
	mem R->(node<@L,@M>);

lseg<R,p> == self = p & R = {}
	or self::node<_@L,q> * q::lseg<Rq,p> & R = union(Rq,{self})
	inv true
	mem R->(node<@L,@M>);

lemma self::ll<R> <-> self::lseg<R,p>;

global node cached;
global node q;

void add_L(node x, ref node y)
requires x::node<v,_@M> * y::ll<Ry>
ensures y'::node<v,y@A> * y::ll<Ry>;
{
  x.next = y;
  y = x;
}

node find_L(ref node q, int k)
requires q::ll<Rq>
ensures q::lseg<R1,res> * res::node<k,q2> * q2::ll<R2> & Rq =union({res},R1,R2);

void caching(node x, ref node cached)
requires x::node<v@L,n@L> * cached::node<_,_>
ensures cached::node<v,n> * x::node<v@L,n@L>;

void add_in(int key, ref node cached, ref node q) 
requires (cached::node<_,_> & q::ll<Rq>) 
ensures  (cached'::node<key,_> & q::ll<R1>) & R1 = union(Rq,{cached'});
{
  node x,tmp;
  tmp = find_L(q,key);
  if(tmp == q || tmp.val != key) {
    x = new node(key,null);
    x.val = key;
    add_L(x,tmp);
    caching(x,cached);
  }
}

node find(int key, ref node cached, ref node q, int flag) 
requires (cached::node<_,_> & q::ll<Rq>)
ensures  (res::node<key,q2> * q2::ll<R2> * cached'::node<key,_> & q::lseg<R1,res>) & Rq = union(R1,R2,{res});
{
  node tmp, cache;
  if(cached != null) {
    cache = cached;
    if(cache.val == key) return cache;
  }
  tmp = find_L(q,key);
  if(tmp != q) {
    if(flag==1) { caching(tmp, cached); }
    return tmp;
  }
  return null;
}
