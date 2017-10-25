#include <stdlib.h>

extern int __VERIFIER_nondet_int(void);

/* void bubbleSort(int numbers[], int array_size) */
/* /\*@ */
/*   requires numbers::Aseg<0, array_size> & array_size > 0 */
/*   ensures numbers::Aseg<0, array_size>; */
/* *\/ */
/* { */
/*     int i, j, temp; */
     
/*     for (i = (array_size - 1); i >= 0; i--) */
/*       /\*@ */
/* 	case{ */
/* 	i>=0 ->  */
/* 	requires numbers::Aseg<0, i+1> & i>=0 & i<array_size */
/* 	ensures numbers::Aseg<0, i+1>; */
/* 	i<0 -> */
/* 	requires emp & i=-1 */
/* 	ensures emp; */
/* 	} */
/*       *\/ */
/*       { */
/*         for (j = 1; j <= i; j++) */
/* 	  /\*@ */
/* 	    case{ */
/* 	    j<=i -> */
/* 	    requires numbers::AsegNE<j-1, i+1> & j>=1 & j<=i & i>=1  */
/* 	    ensures numbers::AsegNE<j-1, i+1>; */
/* 	    j>i -> */
/* 	    requires emp & j>i */
/* 	    ensures emp; */
/* 	    } */
/* 	  *\/ */
/* 	  { */
/*             if (j>1) { */
/* 	      temp = 1; */
/*                 /\* temp = numbers[j-1]; *\/ */
/*                 /\* numbers[j-1] = numbers[j]; *\/ */
/*                 /\* numbers[j] = temp; *\/ */
/*             } */
/*         } */
/*     } */
/* } */
    /*
      case{
      j<=i->
      requires numbers::AsegNE<j-1, i+1> & j>=1 & j<=i & i>=1 
      ensures numbers::AsegNE<j-1, i+1>;
      j>i ->
      requires emp & j>i
      ensures emp;
      }
    */


int main() {
  int array_size = __VERIFIER_nondet_int();
  if (array_size < 1 || array_size >= 2147483647 / sizeof(int)) {
     array_size = 1;
  }
  int* numbers = (int*) alloca(array_size * sizeof(int));

  int i, j, temp;
  for (j = 1; j<=i; i++)
    /*@
      case{
      j<=i->
      requires emp & true
      ensures emp & true;
      j>i ->
      requires emp & true
      ensures emp & true;
      }
    */
    {
      temp;

    }
  return 0;
}
