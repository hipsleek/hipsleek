data node {
  int value;
  node next;
}

ll<n, S> == self = null & n = 0 & S = {} or
  self::node<v, p> * p::ll<n1, S1> & n = n1 + 1 & S = union({v}, S1)
  inv n >= 0;

bool member(int n, node l) 
  requires l::ll<s, S>
  case {
    n in S -> ensures res;
    n notin S -> ensures !res;
  }
{
  while (l != null) 
  
  {
    if (l.value == n) return true;
    else l = l.next;
  }
  return false;
}

int max(node l) 

{
  int m = 0;
  while (l != null) {
    if (l.value > m) m = l.value;
    l = l.next;
  }
  return m;
}

node sort(int n, node l) 

{
  node res = null;
  while (max(l) >= n) {
    if (member(n,l)) res = new IntList(n,res);
    n++;
  }
  return res;
}
