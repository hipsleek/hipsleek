data Boo {
  int val;
}

int get(Boo x)
  requires x::Boo<z+1> & y = z+1 %% z <? @Lo & y <? @Lo & x <? @Lo
  ensures res = z+1 & true %% res <? @Lo;
{
  dprint;
  int z = x.val;
  dprint;
  return z;
}
