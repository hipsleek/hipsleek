/*
  prim pred can have an output compatible type
  need to support boolean operators, like 
    | or &

*/

pred_prim ann<n:int,b:bool>;
// need to support output type of primitive predicate

ann read() 
  requires true
  ensures  res::ann<i,b> & b;

ann add(ann x, ann y) 
  requires x::ann<i,a>@L*y::ann<j,b>@L
  ensures  res::ann<i+j,r> & (r & (a|b) | !r & !(a|b));
// need to support boolean operator

void sanitize(ann x)
  requires x::ann<a,_>
  ensures x::ann<a,b> & !b;

void print_ann(ann x)
  requires x::ann<_,b> & !b
  ensures true;

void main()
  requires true
  ensures true;
{
  ann v;
  v = read();
  sanitize(v);
  print_ann(v);
}
