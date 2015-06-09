int get_step(int x) {
  if (x > 20) {
    return 3;
  } else if (x > 10) {
    return 2;
  }
  return 1;
}

int main()  {
  int y, step;
  if (y > 0) {
    step = -get_step(y);
  } else {
    step = get_step(-y);
  }
  while(y < -3 || y > 3) {
    y = y + step;
  }
  return 0;
}
