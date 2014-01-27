// Data Structures: explicit taint-bit for comparison
data tint { // int with Taint-bit
  int val;
  int taint; // 1: tainted, 0: sanitized
}
data node { // Linked-List with inT
  tint val;
  node next;
}


// Predicates: since we do not have Relations anymore
ll<n,t> == self=null & n=0 & t=0
  or self::node<v,q> * v::tint<_,tn> * q::ll<n-1,t-tn>
                     & tn>=0 & tn<=1 // tn either 0 or 1 (explicit)
  inv n>=0 & t<=n & t>=0 ;

//? WHY DO I NEED THIS???
non_null<n> == self=null & n=0
  or self::node<v,q> * v::tint<_,_> * q::non_null<n-1> & v!=null
  inv n>=0 ;



// SOURCE: Return tainted int
tint SOURCE()
  requires emp
  ensures  res::tint<_,1> ;

// PROPAGATION: Taint-bit Unchanged
tint PROP(tint n)
  requires n::tint<_,t>
  ensures  res::tint<_,t> & res=n ; // Taint-bit Unchanged

// SINK: Accepts only sanitized int
void SINK(tint n)
  requires n::tint<_,0>@L
  ensures  true ;

// SANITIZE: Cleane taint-bit
tint SANITIZE(tint n)
  requires n::tint<_,_>
  ensures  res::tint<_,0> & res=n ;



// Flow of Tainted Integer
void tintFlow()
  requires true
  ensures  true ;
{
  tint a = SOURCE();
  tint b = PROP(a);
  tint c = SANITIZE(b);
  SINK(c);
}




// Linked-List Operations
// - Sanitization of the Entire Linked-List
node sanitize_ll(node xs)
  requires xs::ll<n,t>  & t>=0 // Possibly Tainted
  ensures  res::ll<n,0> & res=xs ;
{
  if( xs==null ) return xs;
  else {
    xs.val = SANITIZE(xs.val);
    sanitize_ll(xs.next);
    return xs;
  }
}

// - Printing (to SINK) of the Entire Linked-List (one-by-one)
void print_ll(node xs)
  requires xs::ll<_,0>@L
  ensures  true ;
{
  if( xs!=null ) {
    SINK(xs.val);
    print_ll(xs.next);
  }
}

// - Safe Print: Only Print untainted
void sprint_ll(node xs)
  requires xs::ll<n,t>@L * xs::node<v,_> & t>=0 & n>0
  ensures  true ;
  requires xs=null ensures true ;
{
  if( xs!=null ) {
    if( xs.val!=null ) {
      if( xs.val.taint==0 ) {
        SINK(xs.val);
      }
    }
    sprint_ll(xs.next);
  }
}

// - Clean Print: Sanitize before Printing
node cprint_ll(node xs)
  requires xs::ll<n,t> * xs::node<v,_> & t>=0 & t<=n & n>0
  ensures  res::ll<n,0> * res::node<v,_> &res=xs ;
  requires xs=null ensures res=xs ;
{
  if( xs!=null ) {
    if( xs.val!=null ) {
      if( xs.val.taint==1 ) {
        xs.val = SANITIZE(xs.val);
      }
      SINK(xs.val);
    }
    cprint_ll(xs.next);
  }

  return xs;
}

// - LL SOURCE
node LL_SOURCE(tint n)
  requires n::tint<v,_>@L
  ensures  res::ll<v,v> * res::non_null<v> ; // WHY MUST SPECIFY NON_NULL???

void LL_SINK(node xs)
  requires xs::ll<_,0>@L
  ensures  true ;



// Flow of Tainted Linked-List
void llFlow1()
  requires true
  ensures  true ;
{
  tint a = SOURCE();
  node b = LL_SOURCE(a);
  node c = sanitize_ll(b);
  print_ll(c);
}


// Flow of Tainted Linked-List
void llFlow2()
  requires true
  ensures  true ;
{
  tint a = SOURCE();
  node b = LL_SOURCE(a);
  node c = sanitize_ll(b);
  sprint_ll(c);
}
// Flow of Tainted Linked-List
void llFlow3()
  requires true
  ensures  true ;
{
  tint a = SOURCE();
  node b = LL_SOURCE(a);
  //node c = sanitize_ll(b);
  node c = cprint_ll(b);
  print_ll(c);
}


// Flow of Tainted Linked-List
void llFlow4()
  requires true
  ensures  true ;
{
  tint a = SOURCE();
  node b = LL_SOURCE(a);
  node c = sanitize_ll(b);
  LL_SINK(c);
}
