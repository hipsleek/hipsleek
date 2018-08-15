data node {
	int fst;
  int snd;
  int third;
  int fourth;
}

global node Positive_RA_Alt_Thresh;

// error() when index is out of array bound
int int_error() requires true ensures false;

void initialize()
  requires Positive_RA_Alt_Thresh::node<a,b,c,d>
  ensures Positive_RA_Alt_Thresh::node<a2,b2,c2,d2> &
  a2 = 400 & b2 = 500 & c2 = 640 & d2 = 740;

{
    Positive_RA_Alt_Thresh.fst = 400;
    Positive_RA_Alt_Thresh.snd = 550; /* constant mutation 550*/
    Positive_RA_Alt_Thresh.third = 640;
    Positive_RA_Alt_Thresh.fourth = 740;
}