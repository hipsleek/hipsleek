void f() {
  int x=0;
  int y=0;
  int *p = &y;
  //p = &x;
  //p = &x; // Just another mention of &x.
  *p = 1;
  int t = x;
  int **pp = &p;
  //@ dprint;
  //@ assert (y' = 1);
  // ==> assert addr_y::int_star<q> & q = 1
  //@ assert (y' = 2 | x'=0);
  **pp = 5;
  //@ assert p'!=null;
  // need to be fixed below
  //@ assert p'::int_star<5>; 
  // assert addr_p'::int_star_star<q> * q::int_star<5>;
  // ==>  assert addr_p'::int_star_star<q> * q::int_star<5>;
  // dprint;
  return;
}

void main()
{
  f();
}

