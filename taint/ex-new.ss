/*
  prim pred can have an output compatible type
  need to support boolean operators, like 
    | or &

*/

pred_prim /* int */ ann<n:int,b:bool>;
// need to support output type of primitive predicate

int read() 
  requires true
  ensures  res::ann<i,true>; // & b;

int add(int x, int y) 
  requires x::ann<i,a>@L*y::ann<j,b>@L
  //ensures  res::ann<i+j,r> & r = (a|b);
  ensures  res::ann<i+j,(a|b)>;
// need to support boolean operator

void sanitize(int x)
  requires x::ann<a,_>
  ensures x::ann<a,false>;// & !b;

void print_int(int x)
  requires x::ann<_,b>@L & !b
  ensures true;

void main()
  requires true
  ensures true;
{
  int v;
  v = read();
  sanitize(v);
  print_int(v);
}

bool eqInt(int x, int y)
  requires x::ann<i,a1>@L * y::ann<j,a2>@L
  ensures  res=(i=j);

bool foo(int x, int y)
  requires x::ann<v1,a1> * y::ann<v2,a2>
  ensures true;
{
  if (eqInt(x,y)) return true;
  else return false;
}

/*
  requires x<<y & y<=z  --> x<=z

  
 */
