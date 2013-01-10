void cprob_stdtr_168()
{
  float j,k,z,f,tz,MACHEP;
	while ((j<=(k-2.0)) && ((tz/f) > MACHEP ))
	  requires f != 0.0
	  case {
	    j > k-2.0  -> requires Term[] ensures true;
	    j <= k-2.0 -> requires Term[Seq{-j @ (-infty,+infty), j<=k-2}] ensures true;
	  }
	{
		j += 2.0;
	}
}
