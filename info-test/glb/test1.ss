int id_glb(int x)
  requires x<?@Lo%@Hi
  ensures res=x & res<?@Lo;
{
  return x;
}

int id_lub(int x)
  requires x<?@Lo#@Hi
  ensures res=x & res<?@Lo;
{
  return x;
}
