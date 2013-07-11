/**
  Copyright (c) Microsoft Corporation.  All rights reserved.

  Assignment into struct fields.
**/
//#include "slayer.h"

struct Globals
{
  int AssocClassList;
  int NumAssocClass;
};


struct Globals g;

void cpy (int src, int dest)
/*@
  requires src != dest
  ensures true;
*/
{
  //FAIL_IF (src == dest) ;
  //@ assert (src != dest);
  return;
}

main()
{
  int dummy;
  g.AssocClassList = 0;
  g.NumAssocClass = &dummy;
  cpy(g.AssocClassList, g.NumAssocClass);
}
