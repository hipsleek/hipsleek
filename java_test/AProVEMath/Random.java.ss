
global String[] Random_args;

global int Random_index = 0;
data Random
{

}
 int Random_random()
{
  String string = Random_args[Random_index];
  Random_index++;
  return String_length();
}



data AProVEMath
{

}
 int AProVEMath_power(int base, int exponent)
{
  if (exponent == 0) {
    return 1;
  } else if (exponent == 1) {
    return base;
  } else if (base == 2) {
    return base << exponent - 1;
  } else {
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

void AProVEMath_main(String[] args)
{
  Random_args = args;
  int x = Random_random();
  int y = Random_random();
  AProVEMath_power(x, y);
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;