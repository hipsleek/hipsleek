void main() {
  int x;
  int *y = &x;
  int **t = &y;
  int ***z = &t;
  int ***u = z;
  ***z = 0;
  **t = 3;
  int m = x;
  //@ assert (m' = 3) ;
  //@ assert (x' = 3) ;
  //@ assert y'::int^<3>;
  //@ assert t'::int^^<3>;
  //@ assert z'::int^^^<3>;
  //@ assert u'::int^^^<3>;
  return;
}
