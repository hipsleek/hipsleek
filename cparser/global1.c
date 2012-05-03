#include <stdio.h>
//run: ../cil/cil-1.4.0/obj/x86_LINUX/cilly.asm.exe global1.c --noPrintLn --dohip --out  out/global1.c.i
int x;

int main() {
  x = x+ 1;
  printf("Hello world\n");
  return 0;
}
