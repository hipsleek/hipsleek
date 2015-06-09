int main() {
  int y;
  while (y< -1 || y > 1) {
    if (y < 0) {
      y = y + 1;
    } else {
      y = y - 1;
    }
  }
  return 0;
}
