// addr-of operator

data int_star {
  int deref;
}

data int_star_star {
  int_star deref;
}

// how come we don't use pass-by-copy here?
// pass-by-copy only for struct?
// how about struct*, do we use pass-by-copy?
int foo(int_star q_ptr)  //&(star_q)
  requires q_ptr::int_star<a>
  ensures q_ptr::int_star<a+1> & res=a+1;
{
  int_star r = q_ptr;
  r.deref = r.deref+1;
  return r.deref;
}

data pair {
    int x;
    int y;
}

int main()
  requires true
  ensures res=4;
{
  int_star addr_x = new int_star(0);  // x ==> addr_x.deref
  addr_x.deref = 5;
  int_star_star addr_r = new int_star_star(null);
  addr_r.deref=addr_x;                // &x ==> addr_x
  addr_x.deref = 2;
  int t=foo(addr_r.deref); //  *&r ==> r 
  int k = addr_x.deref+1;
  addr_x.deref=addr_x.deref+1;
  //return addr_x.deref;
  return addr_r.deref.deref;
}


