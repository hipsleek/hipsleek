// Various algorithms to check for primality of n
// 1) divide n by all   m   such that 1 < m < n
// 2) _______________ ODD m such that _________ 
// 3) _______________________________ 1 < m <= sqrt{n}

relation divides(int m, int n).

// definition
axiom n = 0 |- divides(m,n).
axiom 0 < n < m |- !(divides(m,n)).
axiom divides(m,n) |- divides(m,n-m).
axiom divides(m,n) |- divides(m,n+m).

// and some properties
axiom n = m |- divides(m,n).
axiom n = m*k |- divides(m,n).
axiom divides(m,n) & divides(m,p) |- divides(m,n+p).
axiom divides(m,n) |- divides(m,k*n).
axiom divides(m,n) & divides(n,p) |- divides(m,p).
axiom m > 0 & n > 0 & divides(m,n) |- m <= n.
axiom divides(m,n) |- exists(k : n = m * k).

relation prime(int p).

// definition
axiom prime(p) |- p > 1.
axiom p > 1 & forall(m : m <= 1 | m >= p | !(divides(m,p))) |- prime(p).
axiom prime(p) & divides(m,p) |- m = 1 | m = p | m = -p.
axiom p = a * b & 1 < a < p & 1 < b < p |- !(prime(p)).

// p is not divisible by all m in range [2,3,...,n-1]
relation primerel(int p, int n) ==
	forall(m : m <= 1 | m >= n | !(divides(m,p))).

axiom primerel(n,n) |- prime(n).

axiom prime(n) |- primerel(n,n).

//checkentail n > 0 & primerel(n,p) & p * p > n |- primerel(n,n).
//checkentai !(primerel(n,n)) & n > 0 & p * p > n |- !(primerel(n,p)).
//checkentail n = a * b & 0 <= a <= b |- a * a  <= n.
//checkentail divides(a,n) |- (exists u : divides(u,n) & u * u <= n).
axiom n > 0 & primerel(n,p) & p * p > n |- primerel(n,n).

//checkentail true |- prime(2).
//checkentail true |- !(prime(4)).

axiom primerel(n,i) & !(divides(i,n)) |- primerel(n,i+1).
//checkentail primerel(n,i) & i<n & !(divides(i,n)) & j=i+1 |- primerel(n,j).

//checkentail p > 1 & primerel(p,p) |- prime(p).
//checkentail divides(m,0) |- divides(m,m).
//checkentail divides(m,m) |- divides(m,m*q).
//checkentail 0<=q & n=0+(m*q) & (0+1)<=m & (m+m)<=n & m<=n & 1<=m & 0<=n |- divides(m,n).

axiom true |- (divides(2,n) | divides(2,n+1)).
//checkentail true |- (divides(2,n) | divides(2,n+1)).
//proof by induction
//checkentail n = 0 |- (divides(2,n) | divides(2,n+1)).
//checkentail n > 1 & (divides(2,n-1) | divides(2,n-1+1)) |- (divides(2,n) | divides(2,n+1)).

//checkentail divides(2,n) |- !(divides(2,n+1)).

//checkentail !(divides(2,n)) /* & (divides(2,n) | divides(2,n+1))  */ |- divides(2,n+1).

//checkentail 1 < n & !(divides(2,n)) & !(divides(2,p)) & !(divides(p,n)) & primerel(n,p) |- primerel(n,p+2).

//checkentail 3<=p < n & !(divides(2,p)) & primerel(n,p) & !(divides(p,n)) & !(divides(p+1,n)) |- primerel(n,p+2).

bool isdivby(int n, int m)
	requires true
	ensures res & divides(m,n) or !res & !(divides(m,n));
//{
//	return n % m == 0;
//}

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
	requires primerel(n,i) & 2 <= i <= n
	ensures (res & primerel(n,n) | !res & !(primerel(n,n)));
{
	if (i >= n)
		return true;
	else if (isdivby(n,i))
		return false;
	else {
		// encounter syntactical issue of Z3, solved by adding additional assert/assume so that it can match the argument
		assert primerel(n,i+1);
		assume primerel(n,i+1);
		return is_prime1_helper(n,i+1);
	}
}

// Cannot be verified if we use "|" in place of "or"
// So a case analysis is important here!
bool is_prime2(int n) 
	requires n >= 0
	ensures res & prime(n) or !res & !(prime(n));
{
	if (n < 2)
		return false;
	else if (n == 2)
		return true;
	else if (isdivby(n,2))
		return false;
	else
		return is_prime2_helper(n,3);
}

bool is_prime2_helper(int n, int p)
	requires !(divides(2,n)) & 3 <= p <= n & !(divides(2,p)) & primerel(n,p)
	ensures res & primerel(n,n) or !res & !(primerel(n,n));
{
	if (p >= n)
		return true;
	else if (isdivby(n,p))
		return false;
	else {
		// Issue 1 : cannot show that if p is odd, n is odd then p + 1 does not divide n. Note that this is necessary to derive the fact that p <= n - 2 as well.
		// Issue 2 : require a hint to show that primerel(n,p+1)
		assert divides(2,p+1);
		assume divides(2,p+1);
		assert !(divides(p+1,n));
		assume !(divides(p+1,n));
		assert p+2 <= n;
		assume p+2 <= n;
		assert primerel(n,p+1);
		assume primerel(n,p+1);
		assert primerel(n,p+2);
		assume primerel(n,p+2);
		return is_prime2_helper(n,p+2);
	}
}

bool is_prime3(int n)
	requires n >= 0
	ensures res & prime(n) or !res & !(prime(n));
{
	if (n < 2)
		return false;
	else if (n == 2)
		return true;
	else if (isdivby(n,2))
		return false;
	else
		return is_prime3_helper(n,3);
}


bool is_prime3_helper(int n, int p)
	requires !(divides(2,n)) & 3 <= p <= n & !(divides(2,p)) & primerel(n,p)
	ensures res & primerel(n,n) or !res & !(primerel(n,n));
{
	if (p * p > n)
		return true;
	else if (isdivby(n,p)) {
		// Need a theorem here
		// if p^2 <= n and p >= 3 then p < n
		assert p < n;
		assume p < n;
		return false;
	}
	else {
		assert divides(2,p+1);
		assume divides(2,p+1);
		assert !(divides(p+1,n));
		assume !(divides(p+1,n));
		assert p+2 <= n;
		assume p+2 <= n;
		assert primerel(n,p+1);
		assume primerel(n,p+1);
		assert primerel(n,p+2);
		assume primerel(n,p+2);
		return is_prime3_helper(n,p+2);
	}
}
