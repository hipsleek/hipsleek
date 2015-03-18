void loop (int x, int y, int z, int t)
  infer [@term]
  requires true
  ensures true;
  /*
  case {
    x < 0 & y < 0 -> requires Term ensures true;
    x >= 0 & y >= 0 -> case {
      z >= 1 -> requires Loop ensures false;
      z <= -1 -> requires Loop ensures false;
      z = 0 -> requires Term[x+y] ensures true;
    }
    x >= 0 & y < 0 -> case {
      z >= 1 -> requires Loop ensures false;
      z = 0 | z = -1 -> requires Term[x] ensures true;
      z < -1 -> requires MayLoop ensures true;
    }
    x < 0 & y >= 0 -> case {
      z <= -1 -> requires Loop ensures false;
      z = 0 | z = 1 -> requires Term[y] ensures true;
      z > 1 -> requires MayLoop ensures true;
    }
  }
  */
{
  if (x >= 0 || y >= 0) {
    x = x + z - t - 1;
    y = y + t - z - 1;
    loop(x, y, z, t);
  }
}

int main()
  infer [@term]
  requires true
  ensures true;
{
  int a = __VERIFIER_nondet_int();
  int b = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  if (a != b) {
    return 0;
  }
  /*
  while (x >= 0 || y >= 0) {
    x = x + a - b - 1;
    y = y + b - a - 1;
  }
  */
  loop(x, y, a, b);
  return 0;
}

