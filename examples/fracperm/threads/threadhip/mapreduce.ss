data node {
  int val; 
  node next;	
}

ll<n> == self = null & n = 0 
  or self::node<_, q> * q::ll<n-1> 
  inv n >= 0;

void destroyList(node l)
  requires l::ll<n> & n >= 0 
  ensures l=null;


node createList(int n)
  requires n >= 0 
  ensures res::ll<n>;

int count(node l)
  requires l::ll<n> & n>=0
  ensures l::ll<n> & res=n;
{
  if (l==null) {return 0;}
  else {
    node next = l.next;
    int n = count(next);
    return 1+n;
  }
}

void mapper(node l, ref node ol, ref node el)
  requires l::ll<n> & ol=null & el=null & n>=0
  ensures l::ll<n> * ol'::ll<n1> * el'::ll<n2>  & n=n1+n2;
{
  if (l==null){
    ol = null;
    el = null;
  }else{
    mapper(l.next,ol,el);
    if (l.val %2 != 0 ) {
      ol =  new node(l.val, ol);
    }else{
      el =  new node(l.val, el);
    }
  }
}


void reducer(thrd t, node l, ref int  c)
  requires t::thrd<# l::ll<n> & n>=0 & true #>
  ensures l::ll<n> & c'=n & dead(t); //'
{
  join(t);
  c = count(l);
}

void main()
  requires emp ensures emp;
{
  int n = 10;
  node l = createList(n);
  node el=null,ol=null;
  int c1,c2;

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

  int c= count(l);

  assert(c' = c1' + c2' & c'= n'); 

  destroyList(l);
  destroyList(ol);
  destroyList(el);
}
