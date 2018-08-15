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
global bool High_Confidence;
global int Own_Tracked_Alt_Rate;
global bool Two_of_Three_Reports_Valid;

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
    if (Climb_Inhibit) return Up_Separation + 100;
    return Up_Separation;
}

bool Own_Above_Threat()
     requires true ensures res = (Other_Tracked_Alt < Own_Tracked_Alt);
{
    return (Other_Tracked_Alt < Own_Tracked_Alt) && true;
}

bool Own_Below_Threat()
  requires true ensures res = (Other_Tracked_Alt > Own_Tracked_Alt);
{
  return (Own_Tracked_Alt < Other_Tracked_Alt);
}

bool Non_Crossing_Biased_Climb()
  requires Positive_RA_Alt_Thresh::node<a> & (Alt_Layer_Value = 0) &
      (Climb_Inhibit = false)  & (Up_Separation <= Down_Separation)

  ensures Positive_RA_Alt_Thresh::node<a> & (Alt_Layer_Value = 0) &
      (Climb_Inhibit = false)  & (Up_Separation <= Down_Separation) &

  res = ((Cur_Vertical_Sep >= 300) & (Own_Tracked_Alt > Other_Tracked_Alt)
                & (Up_Separation >= a));

{
    bool result;

    if (Inhibit_Biased_Climb() - Down_Separation >= 0){
       result = (!Own_Below_Threat() ||
          (Own_Below_Threat() && !(Down_Separation >= ALIM())));
    } else {	
       result = Own_Above_Threat() && (Cur_Vertical_Sep >= 300) && (Up_Separation >= ALIM());
    }
    return result;
}
