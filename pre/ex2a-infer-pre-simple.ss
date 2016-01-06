relation R(int i, int j,int k).

void loop(ref int i,int n, int s)
  infer[R]
  requires R(i,n,s)
  ensures  false;
{    
  if (i<n) {
    assert 0<=i & i<s assume true;
  }
  loop(i+1,n,s);
}
/*
# ex2a.ss

[RELASS [R]: ( R(i,n,s)) -->  (n<=i | (i<s & 0<=i)),
RELDEFN R: ( i=v_int_11_1755'-1 & n'<v_int_11_1755' & R(i,n',s')) -->  R(v_int_11_1755',n',s'),
RELDEFN R: ( i=v_int_11_1755'-1 & v_int_11_1755'<=n' & R(i,n',s')) -->  R(v_int_11_1755',n',s')]

# what is this failure?

!!! PROBLEM with fix-point calculation
ExceptionFailure("substitute_args: failure with look_up_rel_args_type")Occurred!

*/
