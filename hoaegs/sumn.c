relation sumsq_ind(int n, int s) ==
  (n = 0 & s = 0 | n > 0 & sumsq_ind(n-1,s-n*n)).

relation sumsq(int n, int s) ==
  n >= 0 & 6 * s = n * (n + 1) * (2 * n + 1).

relation sumn_ind(int n, int s) ==
  (n = 0 & s = 0 | n > 0 & sumn_ind(n-1,s-n)).

relation sumn(int n, int s) ==
  n >= 0 & 2 * s = n * (n + 1).

axiom sumn_ind(n,s) ==> sumn(n,s).

axiom sumn(n,s) ==> sumn_ind(n,s).

// Theorem : 1 + 2 + ... + n <= 1 + 2^2 + ... + n^2
//checkentail sumn(n,s1) & sumsq(n,s2) |- s1 <= s2.
//checkentail sumn_ind(n,s1) & sumsq_ind(n,s2) |- s1 <= s2.

// Using induction on the inductive definition

checkentail sumn_ind(0,s1) & sumsq_ind(0,s2) |- s1 <= s2.

checkentail /*n > 0 & */forall(s3,s4 : !(sumn_ind(n-1,s3)) | !(sumsq_ind(n-1,s4)) | s3 <= s4) & sumn_ind(n,s1) & sumsq_ind(n,s2) |- s1 <= s2.

// Using induction on the explicit formula definition

checkentail sumn(0,s1) & sumsq(0,s2) |- s1 <= s2.

checkentail /*n > 0 & */forall(s3,s4 : !(sumn(n-1,s3)) | !(sumsq(n-1,s4)) | s3 <= s4) & sumn(n,s1) & sumsq(n,s2) |- s1 <= s2.

//checkentail n >= 0 & 2 * s1 = n * (n + 1) & 6 * s2 = n * (n + 1) * (2 * n + 1) |- s1 <= s2.

//checkentail n>0 & forall(s1 : !(sumn_ind(n-1,s1)) | sumn(n-1,s1)) & sumn_ind(n,s) |- sumn(n,s).
/*
int findsum(int n)
  requires n >= 0
  ensures sumn(n, res);
//ensures sumn_ind(n, res);
{
  if (n == 0) return 0;
  else if (n==1) return 1;
  else return n + (n-1)+findsum(n-2) ;
}*/
