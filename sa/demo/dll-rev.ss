//xisa

List* reverse(List* l) {
  ListNode* nil = NULL;  // To make graphs easier to follow.
  ListNode* prev;
  ListNode* curr;
  ListNode* next;

  _spec_assume("add_edge(kind_C[(l) =dllist((nil))=>])");
  prev = nil;
  curr = l;
  next = nil;

  while (curr != NULL) {
    prev = curr->prev;
    next = curr->next;

    curr->prev = next;
    curr->next = prev;

    prev = curr;
    curr = next;

    continue;  // To save state at this point for display.
  }

  return prev;
}
