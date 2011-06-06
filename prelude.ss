//class __DivByZeroErr extends __Error {}

int add___(int a, int b) requires true ensures res = a + b;
int minus___(int a, int b) requires true ensures res = a - b;
int mult___(int a, int b) requires true ensures res = a * b;

int div___(int a, int b) case {
  a >= 0 -> case {
    b >= 1 -> requires true ensures (exists r: a = b*res + r & res >= 0 & 0 <= r <= b-1);
    b <= -1 -> requires true ensures (exists r: a = b*res + r & res <= 0 & 0 <= r <= -b-1);
    -1 < b < 1 -> requires false ensures false;
    /*-1 < b < 1 -> requires true ensures true & flow __DivByZeroErr;*/
    }
  a < 0 -> case {
    b >= 1 -> requires true ensures (exists r: a = b*res + r & res <= -1 & 0 <= r <= b-1);
    b <= -1 -> requires true ensures (exists r: a = b*res + r & res >= 1 & 0 <= r <= -b-1);
    -1 < b < 1 -> requires false ensures false;
    /*-1 < b < 1 -> requires true ensures true & flow __DivByZeroErr;*/
    }
}

int mod___(int a, int b) case {
  a >= 0 -> case {
    b >= 1 -> requires true ensures (exists q: a = b*q + res & q >= 0 & 0 <= res <= b-1);
    b <= -1 -> requires true ensures (exists q: a = b*q + res & q <= 0 & 0 <= res <= -b-1);
    -1 < b < 1 -> requires false ensures false;
  }
  a < 0 -> case {
    b >= 1 -> requires true ensures (exists q: a = b*q + res & q <= -1 & 0 <= res <= b-1);
    b <= -1 -> requires true ensures (exists q: a = b*q + res & q >= 1 & 0 <= res <= -b-1);
    -1 < b < 1 -> requires false ensures false;
  }
}

float add___(float a, float b) requires true ensures res = a + b;
float minus___(float a, float b) requires true ensures res = a - b;
float mult___(float a, float b) requires true ensures res = a * b;
float div___(float a, float b) requires b != 0.0 ensures res = a / b;

bool eq___(int a, int b) case {
    a = b -> requires true ensures res;
    a != b -> requires true ensures !res;}
bool eq___(bool a, bool b) case {
    a = b -> requires true ensures res;
    a != b -> requires true ensures !res;}
bool eq___(float a, float b) case {
    a = b -> requires true ensures res;
    a != b -> requires true ensures !res;}
bool neq___(int a, int b) case {
    a = b -> requires true ensures !res;
    a != b -> requires true ensures res;}
bool neq___(bool a, bool b) case {
    a = b -> requires true ensures !res;
    a != b -> requires true ensures res;}
bool neq___(float a, float b) case {
    a = b -> requires true ensures !res;
    a != b -> requires true ensures res;}
bool lt___(int a, int b) case {
    a <  b -> requires true ensures  res;
    a >= b -> requires true ensures !res;}
bool lt___(float a, float b) case {
    a <  b -> requires true ensures  res;
    a >= b -> requires true ensures !res;}
bool lte___(int a, int b) case {
    a <= b -> requires true ensures  res;
    a >  b -> requires true ensures !res;}
bool lte___(float a, float b) case {
    a <= b -> requires true ensures  res;
    a >  b -> requires true ensures !res;}
bool gt___(int a, int b) case {
    a >  b -> requires true ensures  res;
    a <= b -> requires true ensures !res;}
bool gt___(float a, float b) case {
    a >  b -> requires true ensures  res;
    a <= b -> requires true ensures !res;}
bool gte___(int a, int b) case {
    a >= b -> requires true ensures  res;
    a <  b -> requires true ensures !res;}
bool gte___(float a, float b) case {
    a >= b -> requires true ensures  res;
    a <  b -> requires true ensures !res;}
bool land___(bool a, bool b) case {
  a -> case { b -> requires true ensures res; !b -> requires true ensures !res;}
  !a -> requires true ensures !res;}
bool lor___(bool a, bool b) case {
  a -> requires true ensures res;
  !a -> case { b -> requires true ensures res; !b -> requires true ensures !res;}}
bool not___(bool a) case { a -> requires true ensures !res; !a -> requires true ensures res;}
int pow___(int a, int b) requires true ensures true;
relation update_array(int[] a, int i, int v, int[] r) == true.
int array_get_elm_at___(int[] a, int i) requires true ensures res = a[i];
int[] update___(int[] a, int i, int v) requires true ensures update_array(a,i,v,res);
