int mc91 (int n)
case {
	n>100 -> ensures res=n-10;
	n<=100 -> ensures res=91;
}
{
	if (n > 100) return n-10;
	else {
		int m = mc91(n+11);
		return mc91(m);
	}
}

/*

  infer [post]
  requires true
  ensures true;


  infer [post]
  case {
		n>100 -> ensures true;
		n<=100 -> ensures true;
		}

  infer [post]
  case {
		n>100 -> ensures true;
		n<=100 -> ensures res=91;
		}



*/

