void mpfr_src_set_d_94 ()
{
  float d;
  int exp;
  while (d >= 32768.0)
    case {
      d <  32768.0 -> requires Term[]
                      ensures true;
      d >= 32768.0 -> requires Term[Seq{d @ (0,+infty), d >= 32768.0}]
                      ensures true;
    }
  {
    d *= (1.0 / 65536.0);
    exp += 16;
  }
}
