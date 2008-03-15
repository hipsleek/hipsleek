/** <plaintext>
*
* key_gen.c -- C source file to generate test keys (at random)
*              to insert into an AVL tree
*
* Created 03/01/89 by Brad Appleton
*
* ^{Mods:* }
*
* Fri Jul 14 13:57:44 1989, Rev 1.0, brad(0165)
*
**/

#include <stdio.h>

main() {
  int num, i;

  for (i = 0 ; i < 500 ; i++)  {
    num = rand();
    printf("%d\n", num);
  }/* for */

  exit (0);
}/* main */
