void mpfr_src_set_d_99 ()
{
  float d;
  int exp;
  while (d >= 1.0)
    case {
      d <  1.0 -> requires Term[]
                  ensures true;
      d >= 1.0 -> requires Term[Seq{d @ (0,+infty), d >= 1.0}]
                  ensures true;
    }
  {
    d *= 0.5;
    exp += 1;
  }
}
