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
  if (maxdeg >= 0)
  ans->coeffs = (FFelem*)calloc(maxdeg+1, sizeof(FFelem));
   ans->maxdeg = maxdeg;
  ans->deg = -1;
  return ans;
}

void DUPFFfree(DUPFF x)
{
}

void DUPFFswap(DUPFF x, DUPFF y)
{
}


DUPFF DUPFFcopy(const DUPFF x)
{
  return x;
}

void DUPFFshift_add(DUPFF f, const DUPFF g, int deg, const FFelem coeff)
{
}
