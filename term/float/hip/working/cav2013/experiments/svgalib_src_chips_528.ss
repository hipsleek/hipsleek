// Fref = 14318180
void svgalib_src_chips_526(int Fref, int PSN)
{
  int high_N = 127;
  while (Fref / (PSN * high_N) < 150.0e3)
    requires (Fref = 14318180) & (PSN > 1) & (PSN < 4) & (high_N > 0)
    case {
      Fref / (PSN*high_N) >= 150.0e3 -> requires Term[]
                                        ensures true;
      Fref / (PSN*high_N) < 150.0e3  -> requires Term[Seq{-Fref/(PSN*high_N) @ (-infty,0.0), Fref / (PSN*high_N) < 150.0e3}]
                                        ensures true;
    }
  {
    high_N--;
  }
}
