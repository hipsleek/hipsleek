/*
  Implement map/reduce using multi-join.

  A mapper perfoms map operation. Two reducers join 
  with the mapper, own corresponding resource, and
  perform their corresponding reduce operation.

 */

data node {
  int val; 
  node next;	
}

data list { 
  node h; //head node
}

data count{
  int val;
}

ll<n> == self = null & n = 0 
  or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

//mapper thread
pred_prim MTHRD{(-)P,(+)Q}<l:list,ol:list,el:list>;
pred_prim MTHRD2{(+)Q@Split}<l:list,ol:list,el:list>;

//reducer thread
pred_prim RTHRD{(-)P,(+)Q}<t:thrd,l:list,c:count>;
pred_prim RTHRD2{(+)Q}<t:thrd,l:list,c:count>;

pred_prim DEAD<>;

//normalization of dead threads
lemma "normalize" self::MTHRD2{%Q}<x,y,z> * self::DEAD<> -> %Q;

thrd create_mapper()
  requires true
  ensures (exists l,ol,el: res::MTHRD{l::list<hl> * hl::ll<n> * ol::list<null> * el::list<null> & n>=0, l::list<hl> * hl::ll<n> * ol::list<hol> * hol::ll<n1> * el::list<hel> * hel::ll<n2>  & n=n1+n2}<l,ol,el>);

void fork_mapper(thrd t,list l, list ol, list el)
  requires t::MTHRD{%P,%Q}<l,ol,el> * %P
  ensures  t::MTHRD2{%Q}<l,ol,el>;

void join_mapper(thrd t)
  requires exists l,ol, el: t::MTHRD2{%Q}<l,ol,el>
  ensures  t::DEAD<> * %Q;

thrd create_reducer1()
  requires true
  ensures (exists m,ol,c: res::RTHRD{ m::MTHRD2{ol::list<hol> * hol::ll<n1> & n1>=0 & true}<_,ol,_> * c::count<_> & true, ol::list<hol> * hol::ll<n1> * m::DEAD<> * c::count<n1>}<m,ol,c>);

thrd create_reducer2()
  requires true
  ensures (exists m,el,c: res::RTHRD{ m::MTHRD2{el::list<hel> * hel::ll<n2> & n2>=0 & true}<_,_,el> * c::count<_> &true, el::list<hel> * hel::ll<n2> * m::DEAD<> * c::count<n2> } <m,el,c>);


void fork_reducer(thrd t, thrd m,list l, count c)
  requires t::RTHRD{%P,%Q}<m,l,c> * %P
  ensures  t::RTHRD2{%Q}<m,l,c>;

void join_reducer(thrd t)
  requires exists m,l,c: t::RTHRD2{%Q}<m,l,c>
  ensures  t::DEAD<> * %Q;

//*****************************
void destroyCount(count c)
  requires c::count<_>
  ensures emp;

void destroyL(list l)
  requires l::list<null>
  ensures emp;

void destroyll(node l)
  requires l::ll<n> & n >= 0 
  ensures emp & l=null;

void destroyList(list l)
  requires l::list<hl> * hl::ll<n>
  ensures emp;
{
  destroyll(l.h);
  destroyL(l);
}

node createll(int n)
  requires n >= 0 
  ensures res::ll<n>;

int count_helper(node nl)
  requires nl::ll<n> & n>=0
  ensures nl::ll<n> & res=n;
{
  if (nl==null) {return 0;}
  else {
    node next = nl.next;
    int n = count_helper(next);
    return 1+n;
  }
}

int countList(list l)
  requires l::list<nl> * nl::ll<n> & n>=0
  ensures l::list<nl> * nl::ll<n> & res=n;
{
  return count_helper(l.h);
}

void mapper(list l, list ol, list el)
  requires l::list<hl> * hl::ll<n> * ol::list<null> * el::list<null>
  ensures l::list<hl> * hl::ll<n> * ol::list<hol> * el::list<hel> * hol::ll<n1> * hel::ll<n2>  & n=n1+n2;
{
  node hol = null;
  node hel = null;
  mapper_helper(l.h,hol,hel);
  ol.h = hol;
  el.h = hel;
}

void mapper_helper(node l, ref node ol, ref node el)
  requires l::ll<n> & ol=null & el=null & n>=0
  ensures l::ll<n> * ol'::ll<n1> * el'::ll<n2>  & n=n1+n2;
{
  if (l==null){
    ol = null;
    el = null;
  }else{
    mapper_helper(l.next,ol,el);
    if (l.val %2 != 0 ) {
      ol =  new node(l.val, ol);
    }else{
      el =  new node(l.val, el);
    }
  }
}

void reducer1(thrd m, list ol, count c)
  requires m::MTHRD2{ol::list<hol> * hol::ll<n> & n>=0 &true}<_,ol,_> * c::count<_>
  ensures ol::list<hol> * hol::ll<n> * m::DEAD<> * c::count<n>; //'
{
  join_mapper(m);
  int t = countList(ol);
  c.val = t;
}

void reducer2(thrd m, list el, count  c)
  requires m::MTHRD2{el::list<hel> * hel::ll<n> & n>=0 &true}<_,_,el> * c::count<_>
  ensures el::list<hel> * hel::ll<n> * m::DEAD<> * c::count<n>; //'
{
  join_mapper(m);
  int t = countList(el);
  c.val = t;
}

void main()
  requires emp ensures emp;
{
  int n = 10000;
  node ll = createll(n);
  list l = new list(ll);
  list el= new list(null);
  list ol= new list(null);
  count c1 = new count(0);
  count c2 = new count(0);

  thrd m = create_mapper();
  thrd r1 = create_reducer1();
  thrd r2 = create_reducer2();

  //mapper to classify into two list ol and el
  fork_mapper(m,l,ol,el);

  // the first reducer counts in ol
  fork_reducer(r1,m,ol,c1);

  // the second reducer counts in ol
  fork_reducer(r2,m,el,c2);

  join_reducer(r1);
  join_reducer(r2);


  int n1 = countList(l);
  int n2 = countList(ol);
  int n3 = countList(el);
  assert(n1' = n2' + n3' & n1'= n'); //'

  destroyList(l);
  destroyList(ol);
  destroyList(el);
  destroyCount(c1);
  destroyCount(c2);

  //no need to explicitly destroy t::DEAD<>
  //since they are pure predicates
  //t::DEAD<> * t::DEAD<> -> t::DEAD<>
}

/*
# mapreduce.ss -tp parahip --eps -perm fperm --classic

 where is __false
 where is primitives Line 64?

!!!Full processing file "mapreduce.ss"
Parsing file "mapreduce.ss" by default parser...

!!! processing primitives "["prelude.ss"]
Starting Omega...oc

Last Proving Location: 1 File "primitives",Line:64,Col:0

ERROR: at _0:0_0:0 
Message: Can not find flow of __false
 Stop Omega... 0 invocations caught
(Program not linked with -g, cannot print stack backtrace)

Exception occurred: Failure("Can not find flow of __false")
Error3(s) detected at main 

*/
