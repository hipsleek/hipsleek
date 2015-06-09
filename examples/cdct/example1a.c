int get_step(int x) {
  return 1;
}

int main()  {
  int y, step;
  step = get_step(y);
  if (y > 0) {
    step = -step;
  }
  while(y < -1 || y > 1) {
    y = y + step;
  }
  return 0;
}
