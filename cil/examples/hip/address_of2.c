struct pair {
  int x;
  int y;
};

void main() {
  struct pair p = {3, 4};
  int *y = &p.x;
  int **z = &y;
  **z = 9;
  //@ assert p'::pair<9, _> ;
  return;
}
