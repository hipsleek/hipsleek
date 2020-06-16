data int_star {
  int v;
}

void free_is(int_star v)
  requires v::int_star<_>
  ensures  emp;

class exn extends __Exc{}

void foo() {
  raise new exn();
}

int test()
  requires true
  ensures emp;
{
  int_star addr_a;
  addr_a = new int_star();
  try {
    foo();
    free_is(addr_a);
    return 0;
    dprint;
  }
  catch (__Exc e){
    free_is(addr_a);
    raise e;
    dprint;
  };
}

/*
int test() {
  int a;
}
*/
