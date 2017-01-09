data node {
  int value;
  node left;
  node right;
}

tree<n> == 
  self = null & n = 0 or
  self::node<_, l, r> * l::tree<nl> * r::tree<nr> & n = 1 + nl + nr
  inv n >= 0;
  
node copy(node s) 
  requires s::tree<n> & Term[n]
  ensures res::tree<n> * s::tree<n>;
{
  if (s == null) {
    return null;
  }
  node result = new node();
  result.left = copy(s.left);
  result.right = copy(s.right);
  return result;
}

node alternate(node t, node s) 
  requires t::tree<n1> * s::tree<n2> & Term[n1 + n2]
  ensures res::tree<n1 + n2> * t::tree<n1> * s::tree<n2>;
{
  // from (Dershowitz & Jouannaud 90, p. 253)
  
  if (t == null) {
    return copy(s);
  } else {
    return new node(t.value, copy(t.left), alternate(s, t.right));
  }
}

