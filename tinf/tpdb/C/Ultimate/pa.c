#include "stdhip2.h"

extern int __VERIFIER_nondet_int(void);
//extern int* add___(int* p, int i);

int main() {
  int *p = malloc(2 * sizeof(int));
  int *q = p;
  loop(p, q);
  return 0;
}

void loop(int* p, int* q)
  /*
    infer [@term]
    requires p::int*<vp, op> * q::int*<vq, oq> & op>=0 & oq>=0
    ensures true;
   */
  /*@
    infer [@term]
    requires p::int*<vp, op> & op>=0
    case {
      q = p -> requires Term[vp] ensures true;
      q != p -> requires q::int*<vq, oq> & oq>=0 ensures true;
      //q = p -> requires true ensures true;
      //q != p -> requires q::int*<vq, oq> & oq>=0 & Term[op+1024-oq, vq] ensures true;
    }
   */
   /*
    requires p::int*<vp, op>
    case {
      q = p -> requires Term[vp] ensures true;
      q != p -> requires q::int*<vq, oq> & Term[op+1024-oq, vq] ensures true;
    }
   */
{
  if (*q >= 0 && q < p + 1024) {
    if (__VERIFIER_nondet_int()) {
      (*q)--;
    } else {
      q++;
    }
    loop(p, q);
  }
}

void loop3(int* p, int* q)
  /*
    infer [@term]
    requires p::int*<_, op> * q::int*<vq, oq> & op>=0 & oq>=0
    ensures true;
   */
{
  if (q < p) {
    q++;
    loop3(p, q);
  }
}
