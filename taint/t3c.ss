// Linked-List
data node {
  int val;
  int taint; // 1: tainted, 0: sanitized
  node next;
}


// Predicates: remove Relations
ll<n,t> == self=null & n=0 & t=0
  or self::node<_,tn,q> * q::ll<n-1,t-tn>
                        & tn>=0 & tn<=1
  inv n>=0 & t<=n & t>=0;




// SOURCE, SINK, SANITIZER, PROPAGATION
node SOURCE(int n) requires emp ensures res::ll<n,n> ; // ALL TAINTED
node PROP(node xs) requires xs::ll<_,t>@L ensures res=xs ;
void SINK(node n) requires n::node<_,0,_>@L ensures true ;
node SANITIZE(node n) requires n::node<_,_,q> ensures res::node<_,0,q> & res=n ;



node sanitize_ll(node xs)
  requires xs::ll<n,t>  & t>=0
  ensures  res::ll<n,0> & res=xs ;
{
  if( xs!=null ) {
    xs = SANITIZE(xs);
    sanitize_ll(xs.next);
  }
  return xs;
}

void print_ll(node xs)
  requires xs::ll<_,0>@L
  ensures  true ;
{
  if( xs!=null ) {
    SINK(xs);
    print_ll(xs.next);
  }
}

void sprint_ll(node xs)
  requires xs::ll<n,t>@L & t>=0 & n>=0
  ensures  true ;
{
  if( xs!=null ) {
    //if( xs.val!=null ) {
      if( xs.taint==0 ) {
        assert(xs::node<_,0,_>);
        SINK(xs);
      }
    //}
      sprint_ll(xs.next);
  }
}

void cprint_ll(node xs)
  requires xs::node<v,_,q> * q::ll<n,t> & t>=0 & n>=0
  ensures  res::ll<n+1,0> & res=xs ;
{
  if( xs!=null ) {
    xs = SANITIZE(xs);
    SINK(xs);
    cprint_ll(xs.next);
  }
  return xs;
}




// Flow of Tainted Linked-List
void llFlow2()
  requires true
  ensures  true ;
{
  node a = SOURCE();
  node b = PROP(a);
  node c = sanitize_ll(b);
  sprint_ll(c);
}
// Flow of Tainted Linked-List
void llFlow3()
  requires true
  ensures  true ;
{
  node a = SOURCE();
  node b = PROP(a);
  //node c = sanitize_ll(b);
  node c = cprint_ll(b);
  print_ll(c);
}
