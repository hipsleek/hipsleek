data node {
	int fst;
}

global node Positive_RA_Alt_Thresh;
global int Alt_Layer_Value;
global int Down_Separation;

// error() when index is out of array bound
int int_error() requires true ensures false;

int ALIM()
  requires Positive_RA_Alt_Thresh::node<a> & Alt_Layer_Value = 0
  ensures Positive_RA_Alt_Thresh::node<a> & res = a;
{
  if (Alt_Layer_Value == 0) return Positive_RA_Alt_Thresh.fst;
  return int_error();
}

bool foo()
//requires Positive_RA_Alt_Thresh::node<a> & (Alt_Layer_Value = 0) & (Down_Separation >= a)
requires Positive_RA_Alt_Thresh::node<a> & (Alt_Layer_Value = 0)
ensures res = (Down_Separation >= a);
//ensures res = true;
{
  bool r;
  int a;
  r = (Down_Separation > ALIM());
  return r;
}

