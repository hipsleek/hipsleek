// Fref = 14318180
void svgalib_src_chips_526(int Fref, float PSN)
{
  int low_N = 3;
  while (Fref / (PSN * low_N) > 2.0e6)
    requires (Fref = 14318180) & (PSN > 0.0) & (low_N >= 3)
    case {
      Fref / (PSN*low_N) <= 2.0e6 -> requires Term[]
                                     ensures true;
      Fref / (PSN*low_N) > 2.0e6  -> requires Term[Seq{Fref/(PSN*low_N) @ (0.0,+infty), Fref / (PSN*low_N) > 2.0e6}]
                                     ensures true;
    }
  {
    low_N++;
  }
}
