/** <plaintext>
*
* testvals.h -- test values for avl trees
*
* Created 03/01/89 by Brad Appleton
*
* ^{Mods:* }
*
* Fri Jul 14 13:53:18 1989, Rev 1.0, brad(0165)
*
**/

int TestVals[] = {
  1,
  3,
  2,
  5,
  4,
  7,
  6,
  9,
  8,
 11,
 10,
 13,
 12,
 15,
 14
}; /* TestVals */

#define NUM_VALS   (sizeof(TestVals) / sizeof(int))


int DelVals[] = {
  1,
  2,
  3,
  4,
  5,
  6,
  7,
  8,
  9
#ifdef NEVER
,

 10,
 11,
 12,
 13,
 14,
 15
#endif
}/* DelVals */;

#define NUM_DELS   (sizeof(DelVals) / sizeof(int))
