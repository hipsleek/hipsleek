data Nats { Nats pre; }

nats<v> ==
  self::Nats<null> & v = 0 or
  self::Nats<p> * p::nats<v - 1>
  inv v >= 0;

Nats createNats(int n) 
  case {
    n <= 0 -> requires Term ensures res::nats<0>;
    n > 0 -> requires Term[n] ensures res::nats<n>;
  }
{
  if (n <= 0) return new Nats(null);
  else return new Nats(createNats(n - 1));
}

int toInt(Nats n) 
  requires n::nats<v> & Term[v]
  ensures n::nats<v> & res = v;
{
  if (n.pre == null) {
    return 0;
  }
  return toInt(n.pre) + 1;
}

bool isZero(Nats n) 
  requires n::nats<v> & Term
  ensures n::nats<v> & (v > 0 & !res) | (v <= 0 & res);
{
  return (n.pre == null);
}

Nats zero() 
  requires Term
  ensures res::nats<0>;
{
  return new Nats(null);
}

Nats succ(Nats x) 
  requires x::nats<v> & Term
  ensures res::nats<v + 1>;
{
  Nats y = new Nats(null);
  y.pre = x;
  return y;
}

Nats copy(Nats n) 
  requires n::nats<v> & Term[v]
  ensures n::nats<v> * res::nats<v>;
{
  if (n.pre == null) {
    return new Nats(null);
  }
  Nats predCopy = copy(n.pre);
  return succ(predCopy);
}

// by Thomas Kolbe
Nats div(Nats x, Nats y, Nats z) 
  requires x::nats<xv> * y::nats<yv> * z::nats<zv>
  case {
    zv <= 0 -> requires Term ensures res::nats<_>;
    zv > 0 -> case {
      xv >= yv -> requires Term[xv, xv - yv] ensures res::nats<_>;
      xv < yv -> requires Term[xv] ensures res::nats<_>;
    }
  }
{
  if (isZero(z)) {
    return zero();
  }
  if (isZero(y)) {
    return succ(div(copy(x), copy(z), copy(z)));
  }
  if (isZero(x)) {
    return zero();
  }
  return div(copy(x.pre), copy(y.pre), z);
}

int rand()
  requires Term
  ensures true;

void main() 
  requires Term
  ensures true;
{
  Nats x = createNats(rand());
  Nats y = createNats(rand());
  div(x, y, copy(y));
}


