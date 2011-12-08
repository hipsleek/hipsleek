relation sumsq_ind(int n, int s) ==
  (n = 0 & s = 0 | n > 0 & sumsq_ind(n-1,s-n*n)).

relation sumsq(int j, int s) ==
  j >= 0 & 6 * s = j * (j + 1) * (2 * j + 1).


relation sumn_ind(int n, int s) ==
  (n = 0 & s = 0 | n > 0 & sumn_ind(n-1,s-n)).

relation sumn(int j, int s) ==
  j >= 0 & 2 * s = j * (j + 1).

axiom sumn_ind(n,s) ==> sumn(n,s).

axiom sumn(n,s) ==> sumn_ind(n,s).

//checkentail n>0 & forall(s1 : !(sumn_ind(n-1,s1)) | sumn(n-1,s1)) & sumn_ind(n,s) |- sumn(n,s).

int findsum(int n)
  requires n >= 0
  ensures sumn(n, res);
//ensures sumn_ind(n, res);
{
  if (n == 0) return 0;
  else if (n==1) return 1;
  else return n + (n-1)+findsum(n-2) ;
}
