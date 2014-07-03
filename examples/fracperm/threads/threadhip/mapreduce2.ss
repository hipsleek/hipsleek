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

//*****************************
void destroyL(list l)
  requires l::list<null>
  ensures emp & l=null;

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

void reducer(thrd m, list el, count  c)
  requires m::thrd<# el::list<hel> * hel::ll<n> & n>=0 &true#> * c::count<_>
  ensures el::list<hel> * hel::ll<n> * c::count<n> & dead(m); //'
{
  join(m);
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

  //mapper to classify into two list ol and el
  thrd m = fork(mapper,l,ol,el);

  // the first reducer counts in ol
  thrd r1 = fork(reducer,m,ol,c1);

  // the second reducer counts in ol
  thrd r2 = fork(reducer,m,el,c2);

  //still has m::thrd<list::list<n>> here

  join(m); //currently need to avoid inconsistencies
  // but can be removed later when we support
  // m::thrd<list::list<n>> & dead(m) ==> list::list<n>

  join(r1);

  join(r2);


  int n1 = countList(l);
  int n2 = countList(ol);
  int n3 = countList(el);
  assert(n1' = n2' + n3' & n1'= n'); //'

  destroyList(l);
  destroyList(ol);
  destroyList(el);
}
