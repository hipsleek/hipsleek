/**
 Example: sum of elements of an array.
 **/

// right recursive definition of the sum
//relation sumarray(int[] a, int i, int j, int s) == (i > j & s = 0 | i <= j & ex ( t : sumarray(a,i+1,j,t) & s = t + a[i])).
relation sumarray(int[] a, int i, int j, int s) == (i > j & s = 0 | i = j & s = a[i] | i < j & ex ( t : sumarray(a,i+1,j-1,t) & s = a[i] + t + a[j])).

relation sumarrayL(int[] a, int i, int j, int s) == (i > j & s = 0 | i <= j & ex ( t : sumarrayL(a,i,j-1,t) & s = t + a[j])).

/**
 Compute \sum_{k=i..j}{a[i]} by a[i] + (a[i+1] + (a[i+2] + ... + a[j]))...)
 **/
int sigmaright(int[] a, int i, int j) 
	requires true
	ensures sumarray(a, i, j, res);
{
	int r;
	if (i > j)
		r = 0;
	else 
		r = a[i] + sigmaright(a, i+1, j);
	return r;
}

/**
 Compute \sum_{k=i..j}{a[i]} by ((...(a[i] + a[i+1]) + a[i+2]) + ... + ) + a[j]

 Since sumarray is defined by "right recursion", it is reasonable that we cannot prove the correctness of this function. The system need the ability to perform mathematical induction in order to prove this specification. To be more specific, the formula to do induction on is:

 P(j) := for all i, s, t: if j >= i >= 0 & sumarray(a, i, j-1, s) & t = s + a[j] -> sumarray(a, i, j, t)

 The proof by induction proceeds as follow:

 + Base case j = 0: Since 0 = j >= i >= 0, i = 0. So 

                 0 = i > j-1 = -1

             ==> s = 0
                 t = a[0]. 

Note that since i <= j, so the RHS of P(j) is

       sumarray(a, i, j, a[0]) <-> sumarray(a, i, j-1, s1) & t = a[i] + s1. 

Clearly s1 = 0 as i = 0 > j-1 = -1 and hence, t = a[i] = a[0]. Base case is done.

 + Induction: assume P(j), we want to prove P(j+1) which is

 j+1 >= i >= 0 & sumarray(a, i, j, s) & t = s + a[j+1] -> sumarray(a, i, j+1, t)

Again, by the definition: 

  |- sumarray(a,i,j+1,t) <-> exists s1 : sumarray(a,i+1,j,s1) & t = a[i] + s1

So to prove P(j), we only need to show that

  0 <= i <= j+1 & sumarray(a, i, j, s) & t = s + a[j+1] |- exists s1 : sumarray(a,i+1,j,s1) & t = a[i] + s1

From this, we discover that if such s1 exists, its value must make s + a[j+1] = a[i] + s1. Hence s1 = s + a[j+1] - a[i]. This leads to

 0 <= i <= j+1 & sumarray(a, i, j, s) & t = s + a[j+1] & s1 = s + a[j+1] - a[j] |- sumarray(a,i+1,j,s1)

Now we can remove t to get

 0 <= i <= j+1 & sumarray(a, i, j, s) & s1 = s + a[j+1] - a[j] |- sumarray(a,i+1,j,s1)

    * Case i = j + 1:  i > j and hence s = 0 and t = a[j+1]. Clearly s1 = 0 and so t = a[i]. As i = j+1, a[j+1] = a[i]. So the value of t is consistent.

    * Case i + 1 = j

    * Case i < j + 1:  0 <= i + 1 <= j and hence, the induction hypothesis P(j) gives

        sumarray(a,i+1,j-1,s1) & t1 = s1 + a[j] -> sumarray(a,i+1,j,t1)

Together with the hypothesis

        sumarray(a, i, j, s) & t = s + a[j+1]
 **/
int sigmaleft(int[] a, int i, int j) 
	requires true
	ensures sumarrayL(a, i, j, res);
{
	int r;
	if (i > j)
		r = 0;
	else // need to prove |- P(j) here!
		r = sigmaleft(a, i, j-1) + a[j];
	return r;
}
