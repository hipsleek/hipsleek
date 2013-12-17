template int r(int n, int m).

/*
# Ack-i3-infer.ss

Can we support a lexicographic template?

Can we support relAssumption generation first, and then
to perform solving only during template infer?

Termination checking result:  
 
 (7)->(14) (MayTerm ERR: not decreasing) 
Term[4; r: r_0+(r_n*m)+(r_m*n)] -> Term[4; r: r_0+(r_n*m')+(r_m*v_int_14_868')]

 (7)->(12) (MayTerm ERR: not decreasing) 
Term[4; r: r_0+(r_n*m)+(r_m*n)] -> Term[4; r: r_0+(r_n*v_int_12_864')+(r_m*v_int_12_863')]

 (7) 
(MayTerm ERR: not bounded)[r: r_0+(r_n*m)+(r_m*n)]
*/



int ack (int m, int n)
  requires m>=0 & n>=0 & Term[r(m,n)] ensures res>0;
{
	if (m <= 0) 
		return n + 1;
	else if (n <= 0) 
		return ack(m - 1, 1);
	else 
		return ack(m - 1, ack(m, n - 1));
}

void main ()
requires Term
ensures true;
{
	ack(10, 12);
}
