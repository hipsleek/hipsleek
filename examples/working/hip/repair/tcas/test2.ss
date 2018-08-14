data node {
	int fst;
}

global int Cur_Vertical_Sep;

global int Own_Tracked_Alt;
global int Other_Tracked_Alt;

global node Positive_RA_Alt_Thresh;
global int Alt_Layer_Value;

global int Up_Separation;
global int Down_Separation;

//state variables
global int Other_RAC;			// NO_INTENT, DO_NOT_CLIMB, DO_NOT_DESCEND
global int Other_Capability;		//TCAS_TA, OTHER
global bool Climb_Inhibit;

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
    requires Climb_Inhibit = false ensures Climb_Inhibit = false & res = Up_Separation;
{
    if (Climb_Inhibit) return Up_Separation + 300;
    return Up_Separation;
}
