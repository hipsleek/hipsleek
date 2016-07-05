

data RandomHard
{
int source;

int nextPrimeIndex;
}
 void RandomHard_main(String[] args)
{
  int source = args[0]_length();
  if (source < 1) {
    return;
  }
  RandomHard random = new RandomHard(source);
  int limit = args[1]_length();
  
  int i = 0;
  while (i < limit) {
    RandomHard_getNext();
    ++i;
  }
  
}

int RandomHard_getNext(RandomHard _this)
{
  int prime = RandomHard_findKthPrime(_this, this_nextPrimeIndex);
  ++this_nextPrimeIndex;
  int __res = RandomHard_getPowerOfKInSource(_this, prime);
  return __res;
}

int RandomHard_getPowerOfKInSource(RandomHard _this, int k)
{
  int divisor = this_source;
  int __res = 0;
  while (divisor % k == 0) {
    divisor = divisor / k;
    ++__res;
  }
  return __res;
}

int RandomHard_findKthPrime(RandomHard _this, int k)
{
  int yippi = 0;
  int cand = 1;
  while (yippi < k) {
    ++cand;
    boolean isPrime = RandomHard_checkPrime(_this, cand);
    if (isPrime) {
      ++yippi;
    }
  }
  return cand;
}

boolean RandomHard_checkPrime(int n)
{
  if (n < 2) {
    return false;
  }
  
  int i = 2;
  while (i < n) {
    if (n % i == 0) {
      return false;
    }
    ++i;
  }
  
  return true;
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;