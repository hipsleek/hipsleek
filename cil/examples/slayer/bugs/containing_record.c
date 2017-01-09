/*
  Copyright (c) Microsoft Corporation.  All rights reserved.

  Test frontend's treatment of containing_record.
*/

#include "slayer.h"

typedef void *HANDLE;
typedef unsigned char* PCHAR;
typedef unsigned long ULONG;
typedef ULONG *ULONG_PTR;

typedef struct _LIST_ENTRY {
  struct _LIST_ENTRY *Flink;
  struct _LIST_ENTRY *Blink;
} LIST_ENTRY, *PLIST_ENTRY;

typedef struct _ISOCH_RESOURCE_DATA {
  long long  Size;
  long long  Size1;
  PCHAR Name;
  LIST_ENTRY      IsochResourceList;
  HANDLE          hResource;
} ISOCH_RESOURCE_DATA, *PISOCH_RESOURCE_DATA;

 int main()
{
  PISOCH_RESOURCE_DATA IsochResourceData;
  PISOCH_RESOURCE_DATA cr;
  PLIST_ENTRY listEntry;

  IsochResourceData = (PISOCH_RESOURCE_DATA)SLAyer_malloc(sizeof(ISOCH_RESOURCE_DATA));
  listEntry = &(IsochResourceData->IsochResourceList);

  cr = CONTAINING_RECORD(listEntry, ISOCH_RESOURCE_DATA, IsochResourceList);

  FAIL_IF( ! (cr == IsochResourceData) );
  SLAyer_free(cr);
  return 0;
}








