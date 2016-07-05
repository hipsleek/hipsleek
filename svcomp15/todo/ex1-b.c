#include "stdlib.h"


struct DUPFFstruct
{
  int maxdeg;
  int deg;
  // FFelem *coeffs;
};

typedef struct DUPFFstruct *DUPFF;

DUPFF DUPFFnew(const int maxdeg)
{
  DUPFF ans = (DUPFF)malloc(sizeof(struct DUPFFstruct));
  return ans;
}
