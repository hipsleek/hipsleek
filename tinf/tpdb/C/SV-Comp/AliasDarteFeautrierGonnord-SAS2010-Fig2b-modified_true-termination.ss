/*
 * Program used in the experimental evaluation of the following paper.
 * 2010SAS - Alias,Darte,Feautrier,Gonnord, Multi-dimensional Rankings, Program Termination, and Complexity Bounds of Flowchart Programs
 *
 * Date: 2014
 * Author: Caterina Urban
 */

void main() {
  int x;
  int y;
  while (x >= 2) {
    x--; y = y + x;
    while (y >= x + 1) {
      y--;
      while (y >= x + 3) {
        x++; y = y - 2;
      }
      y--;
    }
    x--; y = y - x;
  }
}

