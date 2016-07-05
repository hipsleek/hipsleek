

data Rational
{
int n;

int d;
}
 void Rational_minus(Rational _this, Rational r)
{
  _this.n = _this.n * r.d - r.n * _this.d;
  _this.d *= r.d;
  Rational_simplify(_this);
}

Rational Rational_times(Rational _this, Rational r)
{
  Rational result = new Rational(_this.n * r.n, _this.d * r.d);
  Rational_simplify(result);
  return result;
}

void Rational_divideBy(Rational _this, Rational r)
{
  _this.n *= r.d;
  _this.d *= r.n;
  Rational_simplify(_this);
}

void Rational_eratosthene(boolean[] T)
{
  
  int i = 0;
  while (i < T.length) {
    T[i] = false;
    i++;
  }
  
  if (T.length <= 4)
    return;
  int number = 1;
  while (number * number < T.length) {
    while (T[++number] && number < T.length)
      {
      }
    ;
    
    int i = 2 * number;
    while (i < T.length) {
      T[i] = true;
      i += number;
    }
    
  }
}

int Rational_min(int a, int b)
{
  if (a < b)
    return a;
  else
    return b;
}

int Rational_abs(int a)
{
  if (a < 0)
    return -1 * a;
  else
    return a;
}

void Rational_simplify(Rational _this)
{
  int nn = Rational_abs(_this, _this.n);
  int dd = Rational_abs(_this, _this.d);
  int limite = Rational_min(_this, nn, dd);
  boolean[] divisible = new boolean[limite + 1];
  Rational_eratosthene(_this, divisible);
  boolean go_on = true;
  while (go_on) {
    go_on = false;
    
    int i = 2;
    while (i <= limite) {
      if (!divisible[i])
        if (nn % i == 0 && dd % i == 0) {
          nn /= i;
          dd /= i;
          limite = Rational_min(_this, nn, dd);
          go_on = true;
          break;
        }
      i++;
    }
    
  }
  if (_this.n >= 0 && _this.d >= 0 || _this.n <= 0 && _this.d <= 0) {
    _this.n = nn;
    _this.d = dd;
  } else {
    _this.n = -1 * nn;
    _this.d = dd;
  }
}

boolean Rational_isZero(Rational _this)
{
  return _this.n == 0;
}



data EquationSystem
{
Rational[][] A;

Rational[] b;

int n;
}
 int EquationSystem_searchRow(EquationSystem _this, int col)
{
