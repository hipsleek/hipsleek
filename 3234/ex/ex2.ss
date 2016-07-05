// Add strongest postcondition for the swap etmhod
// below over cell data structures.

data cell {int val;}

void swap (cell i, cell j)
  requires i::cell<a> & i=j
  ensures  false;
  requires i::cell<a>*j::cell<b>
  ensures  false;
{
	int c=i.val;
	i.val = j.val;
	j.val = c;	
}
