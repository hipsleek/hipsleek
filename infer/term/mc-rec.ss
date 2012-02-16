ranking term_f(int n). 

int mcCarthy (int n)
//infer [term_f]
case {
  n>100 -> requires Term ensures res=n-10;
	n<=100 -> requires Term[100-n] 
      ensures res=91;
}
{
	if (n > 100)
		return n - 10;
	else {
		int m = mcCarthy(n+11);
		return mcCarthy(m);
	}
}

/*
!!! NEW RANK:[ 
 (n<=100) --> (term_f(n))>=0,
 (m_21'=91 & n<=89) --> (term_f(n))>(term_f(m_21')),
 (v_int_14_473'=n+11 & n<=89) --> (term_f(n))>(term_f(v_int_14_473'))]
 (m_21'=n+1 & 90<=n & n<=99) --> (term_f(n))>(term_f(m_21')),

+

*/
