void mpfr_src_set_d_112 ()
{
  float d;
  int exp;
  while (d < 0.5)
    case {
      d <=  0     -> requires Loop
                     ensures false;
      0 < d < 0.5 -> requires Term[Seq{-d @ (-infty, 0), d < 0.5}]
                     ensures true;
      d >= 0.5    -> requires Term[]
                     ensures true;
    }
  {
    d *= 2.0;
    exp -= 1;
  }
}
