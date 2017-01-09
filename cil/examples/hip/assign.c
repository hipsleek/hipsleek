#include <stdio.h>
//run: obj/x86_LINUX/cilly.byte.exe --noPrintLn examples/input.c --out examples/output.c

int foo()
{
  return 1;
}

int yyy;

int zzz = 1;

int main() {
  int x;
  x++;
  x--;
  x += 2;
  x -= 2;
  x *= 2;
  x /= 2;
  return 0;
}
