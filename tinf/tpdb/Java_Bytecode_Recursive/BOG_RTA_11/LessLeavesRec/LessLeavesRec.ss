data node {
  int value;
  node l;
  node r;
}

tree<n> == 
  self = null & n = 0 or
  self::node<_, l, r> * l::tree<nl> * r::tree<nr> & n = 1 + nl + nr
  inv n >= 0;
  
node append(node x, node y) 
  requires x::tree<n1> * y::tree<n2> & Term[n1]
  ensures res::tree<n1 + n2>;
{
  // adds y to the right bottom of x
  if (x == null) return y;
  else return new node(x.value, x.l, append(x.r,y));
}

// checks whether one tree has less leaves than the other
bool lessleaves(node x, node y)
  requires x::tree<n1> & y::tree<n2> & Term[n1 + n2]
  ensures (n1 < n2 & res) or (n1 >= n2 & !res);
{
  if (y == null) {
    return false;
  } else {
    if (x == null) {
      return true;
    } else {
      return lessleaves(append(x.l,x.r), append(y.l,y.r));
    }
  }
}

