data cell {
  int val;
}

void main(cell x, cell y)
  infer[@shape,
  @post_n]
  requires true
  ensures true;
{
    y.val=x.val+1;
}
/*
# cell2ap.ss --sa-dis-error

How come post_n not performed after shape
inference?

void main(cell x, cell y)
  infer[@shape,
  @post_n]
  requires true
  ensures true;
{
    y.val=x.val+1;
}

*/
