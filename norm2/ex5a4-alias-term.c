void loop (int* x, int* y)
{
  while (*x < *y) {
    *x = *x - 1;
    *y = *y + 1;
  }
}

int main () {
  int x = 10;
  loop(&x, &x);
}
