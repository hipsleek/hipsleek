//xisa

void findnbackloop(List* l, int x) {
  ListNode* nil = NULL;  // To make graphs easier to follow.
  ListNode* prev;
  ListNode* curr;

  _spec_assume("add_edge(kind_C[(l) =dllist((nil))=>])");

  curr = l;
  while (curr != NULL) {
    if (curr->data == x) { break; }
    curr = curr->next;
  }

  if (curr != NULL) {
    prev = curr->prev;

    while (prev != NULL) {
      curr = prev;         // To name the middle node.
      prev = prev->prev;
    }
  }
}
