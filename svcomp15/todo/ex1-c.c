#include "stdlib.h"

typedef unsigned int FFelem;

struct DUPFFstruct
{
  int maxdeg;
  int deg;
  FFelem *coeffs;
};

typedef struct DUPFFstruct *DUPFF;

DUPFF DUPFFnew(const int maxdeg)
{
  DUPFF ans = (DUPFF)malloc(sizeof(struct DUPFFstruct));
  ans->coeffs = 0;
  return ans;
}
