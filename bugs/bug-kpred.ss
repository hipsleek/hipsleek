/*

 --eps failed for example kpred below,
   while non-eps succeeded. 

 SOLN : complex constraint to be added to heap view that
        has not been specialized yet.

*/


data node {
	int val;
	int color; /* 0 for red, 1 for black */
	node left;
	node right;
}.

pred kpred<n, z> == self::node<v, 0, l, r> & (n=1 & z=3 | n>1 & z=4)
  inv n>=1 & 3<=z<=4.


pred kpred2<n, z> == self::node<v, 0, l, r> & n=1 & z=3 
   or self::node<v, 0, l, r> &  n>1 & z=4
  inv n>=1 & 3<=z<=4.


checkentail x::kpred<n,z> & n=1 |- z=3 .

checkentail x::kpred<n,z> & n>1 |- z=4 .

checkentail x::kpred2<n,z> & n=1 |- z=3 .

checkentail x::kpred2<n,z> & n>1 |- z=4 .
