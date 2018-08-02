data node {
	int fst;
}

global node Positive_RA_Alt_Thresh;
global int Alt_Layer_Value;
global int Down_Separation;
global bool Climb_Inhibit;
global int Up_Separation;
global int Own_Tracked_Alt;
global int Other_Tracked_Alt;

// error() when index is out of array bound
int int_error() requires true ensures false;

int ALIM()
  requires Positive_RA_Alt_Thresh::node<a> & Alt_Layer_Value = 0
  ensures Positive_RA_Alt_Thresh::node<a> & Alt_Layer_Value = 0 & res = a;
{
  if (Alt_Layer_Value == 0) return Positive_RA_Alt_Thresh.fst;
  return int_error();
}

int Inhibit_Biased_Climb ()
    requires Climb_Inhibit = true ensures Climb_Inhibit = true & res = Up_Separation + 100;
  //  requires Climb_Inhibit = false ensures Climb_Inhibit = false & res = Up_Separation;
{
    if (Climb_Inhibit) return Up_Separation + 100;
    return Up_Separation;
}

bool Own_Above_Threat()
     requires true ensures res = (Other_Tracked_Alt < Own_Tracked_Alt);
{
    return (Other_Tracked_Alt < Own_Tracked_Alt);
}

bool foo()
  requires Positive_RA_Alt_Thresh::node<a> & (Alt_Layer_Value = 0) &
  (Climb_Inhibit = true)  & (Up_Separation + 100 > Down_Separation)

  ensures Positive_RA_Alt_Thresh::node<a> & (Alt_Layer_Value = 0) &
  (Climb_Inhibit = true)  & (Up_Separation + 100 > Down_Separation) &
  res = (Down_Separation >= a);

  requires Positive_RA_Alt_Thresh::node<a> & (Alt_Layer_Value = 0) &
  (Climb_Inhibit = true)  & (Up_Separation + 100 <= Down_Separation)

  ensures Positive_RA_Alt_Thresh::node<a> & (Alt_Layer_Value = 0) &
  (Climb_Inhibit = true)  & (Up_Separation + 100 <= Down_Separation) &
  res = (Other_Tracked_Alt < Own_Tracked_Alt);
{
  bool r;
  int a;
  bool upward_preferred;

  upward_preferred = Inhibit_Biased_Climb() > Down_Separation;
  if (upward_preferred){
     r  = (Down_Separation > ALIM());
  } else {
     r = Own_Above_Threat();
  }
  return r;
}
