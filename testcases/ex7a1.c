//Ex.7: a pointer to a variableis only valid when the variable
//      is in scope.
int *malloc(int size)
/*@
      requires emp
      // ensures  res::arr_seg<q,size>;
      ensures res::int_star<_>;
  }
*/;

void foo(int **a)
/*@
  requires a::int_star_star<v>
  ensures a::int_star_star<v1> * v1::int_star<1>;
*/
{
  int* addr_b = (int*) malloc(sizeof(int*)); 
  *addr_b = 1;
  *a = addr_b;
  //free(addr_b);
}

/*
{local: int b
int b
member access b~~>value = 1
member access a~~>value = b}
}

should be:
int_star addr_b;
addr_b = new int_star();
member access b~~>value = 1
member access a~~>value = b}
free(addr_b)


{local: int_star addr_b,int_star tmp
int_star addr_b
int_star tmp
tmp = (102, ):malloc(1)
addr_b = tmp
member access addr_b~~>value = 1
member access a~~>value = addr_b}
}

*/
