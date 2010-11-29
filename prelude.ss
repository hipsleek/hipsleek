class __DivByZeroErr extends __Error {}
class __NullPointerErr extends __Error {}
class __ArrayOutOfBoundErr extends __Error {}

int add___(int a, int b) requires true ensures res = a + b;
int minus___(int a, int b) requires true ensures res = a - b;
int mult___(int a, int b) requires true ensures res = a * b;

int div___(int a, int b) case {
  a >= 0 -> case {
    b >= 1 -> requires true ensures a = b*res + r & res >= 0 & 0 <= r <= b-1;
    b <= -1 -> requires true ensures a = b*res + r & res <= 0 & 0 <= r <= -b-1;
    -1 < b < 1 -> requires true ensures true & flow __DivByZeroErr;
    }
  a < 0 -> case {
    b >= 1 -> requires true ensures a = b*res + r & res <= -1 & 0 <= r <= b-1;
    b <= -1 -> requires true ensures a = b*res + r & res >= 1 & 0 <= r <= -b-1;
    -1 < b < 1 -> requires true ensures true & flow __DivByZeroErr;
    }
}

int mod___(int a, int b) case {
  a >= 0 -> case {
    b >= 1 -> requires true ensures a = b*q + res & q >= 0 & 0 <= res <= b-1;
    b <= -1 -> requires true ensures a = b*q + res & q <= 0 & 0 <= res <= -b-1;
    -1 < b < 1 -> requires false ensures false;
  }
  a < 0 -> case {
    b >= 1 -> requires true ensures a = b*q + res & q <= -1 & 0 <= res <= b-1;
    b <= -1 -> requires true ensures a = b*q + res & q >= 1 & 0 <= res <= -b-1;
    -1 < b < 1 -> requires false ensures false;
  }
}

float add___(float a, float b) requires true ensures res = a + b;
float minus___(float a, float b) requires true ensures res = a - b;
float mult___(float a, float b) requires true ensures res = a * b;
float div___(float a, float b) requires b != 0.0 ensures res = a / b;
bool eq___(int a, int b) requires true ensures res & a = b or !res & a!= b;
bool eq___(bool a, bool b) requires true ensures res & a = b or !res & a!= b;
bool eq___(float a, float b) requires true ensures res & a = b or !res & a != b;
bool neq___(int a, int b) requires true ensures !res & a = b or res & a!= b;
bool neq___(bool a, bool b) requires true ensures !res & a = b or res & a!= b;
bool neq___(float a, float b) requires true ensures !res & a = b or res & a != b;
bool lt___(int a, int b) requires true ensures res & a < b or a >= b & !res;
bool lt___(float a, float b) requires true ensures res & a < b or a >= b & !res;
bool lte___(int a, int b) requires true ensures res & a <= b or a > b & !res;
bool lte___(float a, float b) requires true ensures res & a <= b or a > b & !res;
bool gt___(int a, int b) requires true ensures a > b & res or a <= b & !res;
bool gt___(float a, float b) requires true ensures a > b & res or a <= b & !res;
bool gte___(int a, int b) requires true ensures a >= b & res or a < b & !res;
bool gte___(float a, float b) requires true ensures a >= b & res or a < b & !res;
bool land___(bool a, bool b) requires true ensures a & b & res or !a & !res or !b & !res;
bool lor___(bool a, bool b) requires true ensures a & res or b & res or !a & !b & !res;
bool not___(bool a) requires true ensures a & !res or !a & res;
int pow___(int a, int b) requires true ensures true;

