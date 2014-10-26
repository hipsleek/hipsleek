void L1 (int i, int j) 

{
  if (i < 10) {
    i++;
    if (i % 2 == 0) {
      L1(i, j);
    }
    L2(i, j);
  }
}

void L2 (int i, int j) {
  if (j < 20) {
    j++;
    if (i % 2 == 0) {
      L2(i, j);
    }
    L1(i, j);
  }
}
