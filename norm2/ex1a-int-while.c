//#include <stdlib.h>

//extern int __VERIFIER_nondet_int(void);

void loop (int xxx)
{
  if (xxx <= 0) return;
  else {
    int yyy = xxx - 1;
    loop(yyy);
  }
}

int main() 
{
  return 0;
}
