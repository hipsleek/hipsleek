#define assert(cond)

typedef unsigned int uint32_t;
typedef unsigned char uint8_t;

#if 0
/*
 * Zero 'n' bytes of memory starting from 's'.
 *
 * 'n' and 's' must be word aligned.
 */
void
memzero(void *s, unsigned int n)
{
    uint8_t *p = s;

    /* Ensure alignment constraints are met. */
    assert((unsigned int)s % 4 == 0);
    assert(n % 4 == 0);

    /* Write out words. */
    while (n != 0) {
        *(uint32_t *)p = 0;
        p += 4;
        n -= 4;
    }
}
#endif

int __pointer_add__int_star__int__(int* p, int i)
/*@
  requires true
  ensures true;
 */
;

void
memzero2(void *s, unsigned int n)
{
  uint8_t *p = 0; // s;

    /* Ensure alignment constraints are met. */
    assert((unsigned int)s % 4 == 0);
    assert(n % 4 == 0);

    /* Write out words. */
    while (n != 0) {
      //*(uint32_t *)p = 0;
      p += 4;
        n -= 4;
    }
}
