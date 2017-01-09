

data Test2
{

}
 void Test2_main(String[] args)
{
  Test2_iter(args.length, args.length % 5, args.length % 4);
}

void Test2_iter(int x, int y, int z)
{
  while (x + y + 3 * z >= 0) {
    if (x > y)
      x--;
    else if (y > z) {
      x++;
      y -= 2;
    } else if (y <= z) {
      x = Test2_add(x, 1);
      y = Test2_add(y, 1);
      z = z - 1;
    }
  }
}

int Test2_add(int v, int w)
{
  return v + w;
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;