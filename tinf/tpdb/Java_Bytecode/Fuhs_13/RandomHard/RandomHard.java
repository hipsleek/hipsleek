/**
 * Rather inefficient random number generator that can generate infinitely
 * many positive integers from a single positive integer (the
 * "random source") by taking the exponents of its prime factorization.
 */
public class RandomHard {

  // a single natural number, to give rise to infinitely many natural numbers
  // from its prime factorization (if the datatype int had infinite precision)
  final private int source;

  // use the exponent of the nextPrimeIndex-th prime in the unique
  // prime factorization of source as the next "randomly generated"
  // natural number
  private int nextPrimeIndex;
  
  public RandomHard(int source) {
    this.source = source;
    this.nextPrimeIndex = 1;
  }

  public static void main(String[] args) {
    int source = args[0].length();

    if (source < 1) {
      return;
    }
    RandomHard random = new RandomHard(source);
    int limit = args[1].length();
    for (int i = 0; i < limit; ++i) {
      random.getNext();
    }
  }
  
  /** @return the next (random!) natural number */
  public int getNext() {
    int prime = findKthPrime(this.nextPrimeIndex);
    ++this.nextPrimeIndex;
    int res = getPowerOfKInSource(prime);
    return res;
  }

  /** @return How often can we divide source by k without remainder? */
  private int getPowerOfKInSource(int k) {
    /*if (k < 2) {
      throw new RuntimeException("Divide only by primes -- they are >= 2!");
    }*/
    int divisor = this.source;
    int res = 0;
    while (divisor % k == 0) {
      divisor = divisor / k;
      ++res;
    }
    return res;
  }
  
  /** @return the k-th prime number for k &gt; 0 */
  private int findKthPrime(int k) {
    int yippi = 0;
    int cand = 1;
    // termination of this loop on the integers follows from
    // the existence of infinitely many prime numbers
    while (yippi < k) {
      ++cand;  // all prime numbers are >= 2, so increment
      boolean isPrime = checkPrime(cand);
      if (isPrime) {
        ++yippi;
      }
    }
    return cand;
  }

  /** @return Is n prime? */
  private static boolean checkPrime(int n) {
    if (n < 2) {
      return false;
    }
    for (int i = 2; i < n; ++i) {
      if (n % i == 0) { // i divides n and 1 < i < n
        return false;
      }
    }
    return true;
  }
}
