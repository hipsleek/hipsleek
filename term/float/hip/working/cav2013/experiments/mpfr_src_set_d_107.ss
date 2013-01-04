void mpfr_src_set_d_107 ()
{
  float d;
  int exp;
  while (d < (1.0 / 65536.0))
    case {
      d <=  0             -> requires Loop
                             ensures false;
      0 < d < 1.0/65536.0 -> requires Term[Seq{-d @ (-infty, 0), d < 1.0/65536.0}]
                             ensures true;
      d >= 1.0/65536.0    -> requires Term[]
                             ensures true;
    }
  {
    d *= 65536.0;
    exp -= 16;
  }
}
