void svgalib_threeDKit_3dtext_111 (float t, float PI, int g)
{
  float alpha;
  while (alpha < (2.0*PI/3.0 + t + 0.001))
    requires (PI > 0.0) & (t > 0.0) & (g > 0)
    case {
      alpha >= (2.0*PI/3.0 + t + 0.001) -> requires Term[]
                                           ensures true;
      alpha < (2.0*PI/3.0 + t + 0.001)  -> requires Term[Seq{-alpha @ (-infty,+infty), alpha < (2.0*PI/3.0 + t + 0.001)}]
                                           ensures true;      
    }
  {
    alpha += (2.0*PI/3.0)/g;
  }
}
