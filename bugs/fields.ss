data pair {
 int x;
 int y;
}

void main() {
 pair p = new pair(3, 4);
 int y = p.y;
 p.y = 10;
 y = p.y;
 int z = y;
 assert z'=3;
 return;
}
