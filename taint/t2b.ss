// Linked-List Node
data node {
  int val;
  node next;
}

// Relations (use z3 to proof)
relation tainted(int x).
relation sanitize(int x).


// Predicates:
// - s_ll = Sanitized Linked-List
s_ll<n> == self=null & n=0
  or self::node<v,q> * q::s_ll<n-1> & sanitize(v)
     inv n>=0;

// - t_ll = (Possibly) Tainted Linked-List
t_ll<n> == self=null & n=0
  or self::node<v,q> * q::t_ll<n-1> 
     inv n>=0;

int readS () 
  requires emp
  ensures  emp & tainted(res) ;

int cleanse (int xs) 
  requires emp
  ensures  emp & sanitize(res) ;

int prop (int xs) 
  requires emp
  ensures  res=xs ;

void writeData (int xs) 
  requires emp & sanitize(xs)
  ensures  emp ;


// Simple Sanitization of Linked-List
node szlist(node xs)
  requires xs::t_ll<n>
  ensures  res::s_ll<n> & res=xs;
{
  if (xs==null) return xs;
  else {
    szlist(xs.next);
    xs.val = cleanse(xs.val);
    return xs;
  }
}
