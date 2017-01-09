void nd_loop(int x, int nd1, int nd2)
  infer [@term]
  requires true
  ensures true;
{
  if (x >= 0) {
    if (nd1 > 0)
      nd_loop(x + nd2, nd1, nd2);
    else
      nd_loop(x - nd2, nd1, nd2);
  }
  else return;
}
