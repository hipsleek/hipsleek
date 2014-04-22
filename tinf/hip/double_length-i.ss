template int f(int x, int y).
template int g(int x).

relation R (int x, int y).

data node { int val; node next; }

ll<r> ==
  self = null & r = 0 or
  self::node<v, p> * p::ll<r1> & r = f(v, r1);

int length (node x) 
  infer[f, R]
  requires x::ll<r>@L & Term[r]
  ensures R(r, res);
{
  if (x == null) return 0;
  else return 1 + length(x.next);
}

int rand ()
  requires Term
  ensures true;

/*
node double (node x, int i)
  requires x::ll<r> 
  ensures true;
{
  if (i >= length(x)) 
    return x;
  else
    return double(new node(rand(), x), i + 2);
}
*/
