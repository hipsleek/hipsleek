void svgalib_threeDKit_3dtext_179 (float PI, float GridDensity)
{
  float alpha;
  while (alpha < (2.0*PI + 0.001))
    requires (PI > 0.0) & (GridDensity > 0.0)
    case {
      alpha >= (2.0*PI + 0.001) -> requires Term[]
                                   ensures true;
      alpha < (2.0*PI + 0.001)  -> requires Term[Seq{-alpha @ (-infty,+infty), alpha < (2.0*PI + 0.001)}]
                                   ensures true;      
    }
  {
    alpha += (2.0*PI) / (GridDensity*4);
  }
}
