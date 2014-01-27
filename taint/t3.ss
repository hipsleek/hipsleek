// Linked-List Node
data node {
  int val;
  node next;
}

// Relations
relation sanitized(int x).
relation tainted(int x).


// Predicates:
// - s_ll = Sanitized Linked-List
s_ll<n> == self=null & n=0
  or self::node<v,q> * q::s_ll<n-1> & sanitized(v)
  inv n>=0;

// - t_ll = (Possibly) Tainted Linked-List
t_ll<n> == self=null & n=0
  or self::node<v,q> * q::t_ll<n-1>
  inv n>=0;


// Read Integer:
// - res >= 0 because I need it for creating Linked-List
int readS () 
  requires emp
  ensures emp & tainted(res) & res>=0 ;
  // added condition res >= 0 because ll<n> & n >= 0

// Read Linked-List Node
node readT (int n)
  requires emp & n>=0
  ensures res::t_ll<n> ; // Create Linked-List with specified size (tainted)

// Sanitize a Single Integer Value
int cleanse (int xs) 
  requires emp
  ensures emp & sanitized(res) ;

// Propagate Value
int prop (int xs) 
  requires emp
  ensures  res=xs ;


// SINKS:
// 1. Integer Sink: only accept sanitized Int
void writeData (int xs) 
  requires emp & sanitized(xs)
  ensures emp ;

// 2. Node Sink: only accept sanitized LL
void writeData(node xs)
  requires xs::s_ll<_>@L
  ensures  true ;


// Flow of Int from Source-Sink with Sanitizer
void intFlow()
  requires true
  ensures true;
{
  int x = readS();
  int a = prop(x);
  int b = cleanse(a);
  writeData(b);
}

// Flow of LL from Source-Sink with Recursive Sanitizer
// - Send the entire LL to Sink
void LLFlow()
  requires true
  ensures  true;
{
  int  x = readS();
  node y = readT(x);
  node z = szlist(y);
  writeData(y);
}

// Flow of LL from Source-Sink with Recursive Sanitizer
// - Print one-by-one
void LLFlow2()
  requires true
  ensures  true;
{
  int  x = readS();
  node y = readT(x);
  node z = szlist(y);
  printlist(z);
}

// Flow of LL from Source-Sink with Recursive Sanitizer
// - Double Sanitization Process
// - Print one-by-one
void LLFlow3()
  requires true
  ensures  true;
{
  int  x = readS();
  node y = readT(x);
  node z = szlist(y);
  node w = szlist(z);
  printlist(w);
}



// Print LL by Printing One-by-One Recursively
void printlist(node xs)
  requires xs::s_ll<n>
  ensures xs::s_ll<n>;
{
  if(xs!=null) {
    writeData(xs.val);
    printlist(xs.next);
  }
}



// Recursive Sanitization Process for Linked-List
node szlist(node xs)
  requires xs::t_ll<n>
  ensures  res::s_ll<n> & res=xs;

  // Requires duplicated pre-condition for now
  requires xs::s_ll<n>
  ensures  res::s_ll<n> & res=xs;
{
  if (xs==null) return xs;
  else {
    xs.val = cleanse(xs.val);
    szlist(xs.next);
    return xs;
  }
}
