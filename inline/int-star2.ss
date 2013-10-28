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
int foo(int_star star_q)  //&(star_q)
  requires star_q::int_star<a>
  ensures star_q::int_star<a+1> & res=a+1;
{{
  int_star r = star_q;
  r.deref = r.deref+1;
  return r.deref;
}

int main()
  requires true
  ensures res=3;
{
  int_star addr_x = new int_star(0);  // x ==> addr_x.deref
  int_star r = addr_x;                // &x ==> addr_x
  addr_x.deref = 2;
  int t=foo(r); //  *&r ==> r 
  return t;
}


