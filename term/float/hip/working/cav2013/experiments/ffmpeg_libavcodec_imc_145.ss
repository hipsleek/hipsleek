float freq2bark(float x)
  requires Term[]
  ensures true;

void ffmpeg_libavcodec_imc_145()
{
  float tf;
  float tb;
  float nyquist_freq;
  float bark;
  while (tf < nyquist_freq)
    case {
      tf >= nyquist_freq -> requires Term[]
                            ensures true;
      tf < nyquist_freq  -> requires Term[Seq{-tf @ (-infty,+infty), tf < nyquist_freq}]
                            ensures true;
    }
  {
    tf += 0.5;
    tb = freq2bark(tf);
    if (tb > bark + 0.5)
      break;
  }
}
