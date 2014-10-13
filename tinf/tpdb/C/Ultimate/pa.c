#include "stdhip2.h"

extern int __VERIFIER_nondet_int(void);
//extern int* add___(int* p, int i);

int main() {
  int *p = malloc(2 * sizeof(int));
  int* q = *p;
  //loop(p, q);
  return 0;
}

void loop(int* p, int* q)
  /*@
    infer [@term]
    requires p::int*<_, op, sp> * q::int*<vq, oq, sq> //& Term[op+1024-oq, vq]
    ensures true;
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

void loop2(int* p)
  /*@
    infer [@term]
    requires p::int*<vp, op, sp> & Term[vp]
    ensures true;
   */
{
  if (*p >= 0) {
    (*p)--;
    loop2(p);
  }
}

void loop3(int* p, int* q)
  /*@
    //infer [@term]
    requires p::int*<_, op, sp> * q::int*<vq, oq, sq> 
    ensures true;
    //case {
    //  oq < op -> requires Term[op-oq] ensures true;
    //  oq >= op -> requires Term ensures true;
    //}
   */
{
  if (q < p) {
    q++;
    loop3(p, q);
  }
}
