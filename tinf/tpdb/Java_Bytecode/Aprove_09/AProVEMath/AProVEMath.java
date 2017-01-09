/**
 * Abstract class to provide some additional mathematical functions
 * which are not provided by java.lang.Math.
 *
 * @author fuhs
 */
public abstract class AProVEMath {

  /**
   * Returns <code>base<sup>exponent</sup></code>.
   * Works considerably faster than java.lang.Math.pow(double, double).
   *
   * @param base base of the power
   * @param exponent non-negative exponent of the power
   * @return base<sup>exponent</sup>
   */
  public static int power (int base, int exponent) {
    if (exponent == 0) {
      return 1;
    }
    else if (exponent == 1) {
      return base;
    }
    else if (base == 2) {
      return base << (exponent-1);
    }
    else {
      int result = 1;
      while (exponent > 0) {
        if (exponent % 2 == 1) {
          result *= base;
        }
        base *= base;
        exponent /= 2;
      }
      return result;
    }
  }

  public static void main(String[] args) {
    Random.args = args;
    int x = Random.random();
    int y = Random.random();
    power(x, y);
  }
}
