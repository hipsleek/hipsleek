data node {
  int value;
  node next;
}

ll<n, mx, S> == self = null & n = 0 & mx = 0 & S = {} or
  self::node<v, p> * p::ll<n1, mx1, S1> & 
  n = n1 + 1 & S = union({v}, S1) &
  (v > mx1 & mx = v | v <= mx1 & mx = mx1)
  inv n >= 0 & mx >= 0 & forall(x: (x notin S | x <= mx));

bool member(int n, node l) 
  requires l::ll<s, _, S>@L & Term[s]
  case {
    n in S -> ensures res;
    n notin S -> ensures !res;
  }
{
  if (l == null) return false;
  else if (l.value == n) return true;
  else return member(n, l.next);
}

int mx(node l) 
  requires l::ll<s, mx, S>@L & Term[s]
  ensures (mx < 0 & res = 0 | mx >= 0 & res = mx);
{
  int m = 0;
  node cur = l;
  while (cur != null) 
    requires cur::ll<s, mx, S>@L & Term[s]
    case {
      mx < m -> ensures m' = m;
      mx >= m -> ensures m' = mx;
    }
  {
    if (cur.value > m) m = cur.value;
    cur = cur.next;
  }
  return m;
}

// Check boundedness at loop (using --term-dis-bnd-pre)
node sort(int n, node l) 
  requires l::ll<s, mx, S>@L & Term
  ensures true;
{
  node rs = null;
  while (mx(l) >= n) 
    requires l::ll<s, mx, S>@L
    case {
      mx < 0 -> requires Term[0 - n] ensures true;
      mx >= 0 -> requires Term[mx - n] ensures true;
    }
  {
    if (member(n, l)) 
      rs = new node(n, rs);
    n++;
  }
  return rs;
}


