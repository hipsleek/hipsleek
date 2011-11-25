// Various algorithms to check for primality of n
// 1) divide n by all   m   such that 1 < m < n
// 2) _______________ ODD m such that _________ 
// 3) _______________________________ 1 < m <= sqrt{n}

relation divides(int m, int n) ==
	exists(k : n = m * k).

relation prime(int p) ==
	p > 1 & forall(m : m = 1 | m = p | !(divides(m,p))).

// Check if n is prime by trying to divide n by all 1 < m < n
bool is_prime(int n)
	requires n >= 0
	ensures (res & prime(n) | !res & !(prime(n)));
{
	if (n < 2)
		return false;
	else
		return is_prime_helper(n,2);
}

bool is_prime_helper(int n, int i)
{
	if (i >= n)
		return true;
	else
		return (n % i != 0 && is_prime_helper(i+1));
}

bool is_prime_sq(int n)
{

}
