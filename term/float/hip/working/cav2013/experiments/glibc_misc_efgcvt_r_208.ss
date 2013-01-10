void glibc_misc_efgcvt_r_208()
{
  float d;
  float f;
  while (d * f < 1.0)
    case {
      d*f <= 0      -> requires Loop
                       ensures false;
      0 < d*f < 1.0 -> requires Term[Seq{-d*f @ (-infty,0), d*f < 1.0}]
                       ensures true;
      d*f >= 1.0    -> requires Term[]
                       ensures true;
    }
  {
    f *= 10.0;
  }
}
