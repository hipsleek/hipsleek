// this improved translation will
// avoids @C. Let us use the option --c-para-deref to
// enable it

data int_star{
  int deref;
}

data int_star_star{
  int_star deref;
}

int foo(int_star q_deref)
 requires q_deref::int_star<a>
 ensures q_deref::int_star<a> & res=0;
{
 q_deref = null;
 return 0;
}

int main()
 requires true
 ensures true;
{
 int x;
 int_star addr_x = new int_star(x);
 int_star_star addr_r = new int_star_star(addr_x);
 //int* r = &x;
 foo(addr_r.deref);
 return addr_x.deref;
}
