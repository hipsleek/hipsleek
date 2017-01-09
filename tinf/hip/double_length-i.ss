template int f(int x, int y).

data node { int val; node next; }

ll<n> ==
  self = null & n = 0 or
  self::node<v, p> * p::ll<n1> & n = 1 + n1
  inv n >= 0;

int length (node x) 
  requires x::ll<n>@L & Term[n]
  ensures res = n;
{
  if (x == null) return 0;
  else return 1 + length(x.next);
}

int rand ()
  requires Term
  ensures true;

/* ./hip double_length-i.ss --term-dis-bnd-pre */
node double (node x, int i) 
  infer[f]
  requires x::ll<n> & Term[f(n, i)]
  ensures true;
{
  if (i >= length(x)) 
    return x;
  else
    return double(new node(rand(), x), i + 2);
}

