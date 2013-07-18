data int__star {
 int pdata;
}

pred_prim memLoc<heap:bool,size:int>
  inv size>0;

int__star heap_alloc_int_star(int n) 
  requires n>0
  ensures res::int__star<_> * z::memLoc<h,n> & h;

int__star stack_alloc_int_star(int n) 
  requires n>0
  ensures res::int__star<_> * z::memLoc<h,n> & !h;


void free_heap(int__star p)
 requires p::int__star<n> * z::memLoc<h,n> & h // FAIL here, in "true"
 ensures emp;



void foo (bool b)
  requires b  // FAIL here, in "true"
  ensures true;
{
  int__star p = stack_alloc_int_star(1);
  free_heap(p);
}
