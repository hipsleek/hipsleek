//xisa

dllist* copy(dllist* l) {
  dllist* nil = NULL;  // To make graphs easier to follow.
  dllist* curr;

  dllist* newprev;
  dllist* new;
  dllist* result;

  _spec_assume("def_checker(dllist,dllist,96)" );
  _spec_assume("add_edge(kind_C[(l) =dllist((nil))=>])");

  curr = l;

  if (curr != NULL) {
    newprev = nil;
    new = malloc(sizeof(dllist));
    new->next = NULL;
    new->prev = newprev;
    new->data = curr->data;
    result = new;
    newprev = new;

    while (curr != NULL) {
      new = malloc(sizeof(dllist));
      new->next = NULL;
      new->prev = newprev;
      new->data = curr->data;
      newprev->next = new;
      
      newprev = new;
      
      curr = curr->next;
    }

    return result;
  }
  else {
    return nil;
  }
}
