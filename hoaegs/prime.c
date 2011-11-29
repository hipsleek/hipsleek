// Various algorithms to check for primality of n
// 1) divide n by all   m   such that 1 < m < n
// 2) _______________ ODD m such that _________ 
// 3) _______________________________ 1 < m <= sqrt{n}

relation divides(int m, int n).

// definition
axiom true ==> divides(m,0).
axiom 0 < n < m ==> !(divides(m,n)).
axiom divides(m,n) ==> divides(m,n-m).
axiom divides(m,n) ==> divides(m,n+m).
// and some properties
axiom divides(m,n) & divides(m,p) ==> divides(m,n+p).
axiom divides(m,n) ==> divides(m,k*n).
axiom divides(m,n) & divides(n,p) ==> divides(m,p).
axiom m > 0 & n > 0 & divides(m,n) ==> m <= n.
axiom divides(m,n) ==> exists(k : n = m * k).

relation prime(int p).

// definition
axiom prime(p) ==> p > 1.
axiom p > 1 & forall(m : m <= 1 | m >= p | !(divides(m,p))) ==> prime(p).
axiom prime(p) & divides(m,p) ==> m = 1 | m = p | m = -p.
axiom p = a * b & 1 < a < p & 1 < b < p ==> !(prime(p)).

// p is not divisible by all m in range [2,3,...,n-1]
relation primerel(int p, int n) ==
	forall(m : m <= 1 | m >= n | !(divides(m,p))).

//checkentail true |- prime(2).
//checkentail true |- !(prime(4)).
//checkentail primerel(n,i) & i<n & !(divides(i,n)) |- primerel(n, 1 + i).
//checkentail p > 1 & primerel(p,p) |- prime(p).


// Check if n is prime by trying to divide n by all 1 < m < n
bool is_prime1(int n)
	requires n >= 0
	ensures (res & prime(n) | !res & !(prime(n)));
{
	if (n < 2)
		return false;
	else
		return is_prime1_helper(n,2);
}

bool is_prime1_helper(int n, int i)
	requires primerel(n, i)
	ensures (res & primerel(n,n) | !res & !(primerel(n,n)));
{
	if (i >= n)
		return true;
	else if (isdivby(n,i))
		return false;
	else 
		return is_prime1_helper(n,i+1);
}

bool isdivby(int n, int m)
	requires true
	ensures res & divides(m,n) or !res & !(divides(m,n));


/*
bool is_prime2(int n) {
	return true;
}

bool is_prime_sq(int n)
{
	return false;
}
*/
