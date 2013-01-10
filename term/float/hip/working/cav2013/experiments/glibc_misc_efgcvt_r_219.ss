void glibc_misc_efgcvt_r_219()
{
  float d;
  float f;
  while (d >= f * 10.0)
    case {
      (d <= 0.0) & (d >= f*10.0) -> requires Loop
                                    ensures false;
      (d <= 0.0) & (d < f*10.0)  -> requires Term[]
                                    ensures true;
      (d > 0.0)  & (f <= 0.0)    -> requires Loop
                                    ensures false;
      (d > 0.0)  & (f > 0.0)  & (d >= f*10.0) ->
          requires Term[Seq{-f @ (-infty, 0.0), d >= f*10.0 }]
          ensures true;
      (d > 0.0)  & (f > 0.0)  & (d < f*10.0)  -> requires Term[]
                                                 ensures true;
    }
  {
    f *= 10.0;
  }
}
