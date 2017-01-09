data cell {
  int val;
}


void main(cell x, cell y)
  infer[@shape,
        @post_n,@term
        ]
  requires true
  ensures true;
{
    y.val=x.val+1;
}


/*
void main1(cell x, cell y)
  infer[   @post_n,@term
        ]
  requires x::cell<a>*y::cell<b>
  ensures  x::cell<c>*y::cell<d>;
{
    y.val=x.val+1;
}
*/

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
