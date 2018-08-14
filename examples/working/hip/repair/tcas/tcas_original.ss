data node {
	int fst;
  int snd;
  int third;
  int fourth;
}

global node Positive_RA_Alt_Thresh;
global int Alt_Layer_Value;
global int Down_Separation;
global bool Climb_Inhibit;
global int Up_Separation;
global int Own_Tracked_Alt;
global int Own_Tracked_Alt_Rate;
global int Other_Tracked_Alt;
global int Cur_Vertical_Sep;
global bool High_Confidence;
global bool Two_of_Three_Reports_Valid;
global int Other_RAC;
global int Other_Capability;		/* TCAS_TA, OTHER */

// error() when index is out of array bound
int int_error() requires true ensures false;

int ALIM()
  requires Positive_RA_Alt_Thresh::node<a,b,c,d> & Alt_Layer_Value = 0
  ensures Positive_RA_Alt_Thresh::node<a,b,c,d> & Alt_Layer_Value = 0 & res = a;
  requires Positive_RA_Alt_Thresh::node<a,b,c,d> & Alt_Layer_Value = 1
  ensures Positive_RA_Alt_Thresh::node<a,b,c,d> & Alt_Layer_Value = 1 & res = b;
  requires Positive_RA_Alt_Thresh::node<a,b,c,d> & Alt_Layer_Value = 2
  ensures Positive_RA_Alt_Thresh::node<a,b,c,d> & Alt_Layer_Value = 2 & res = c;
  requires Positive_RA_Alt_Thresh::node<a,b,c,d> & Alt_Layer_Value = 3
  ensures Positive_RA_Alt_Thresh::node<a,b,c,d> & Alt_Layer_Value = 3 & res = d;
{
  if (Alt_Layer_Value == 0) return Positive_RA_Alt_Thresh.fst;
  if (Alt_Layer_Value == 1) return Positive_RA_Alt_Thresh.snd;
  if (Alt_Layer_Value == 1) return Positive_RA_Alt_Thresh.third;
  if (Alt_Layer_Value == 1) return Positive_RA_Alt_Thresh.fourth;
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
  requires Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) &
      (Climb_Inhibit = true)  & (Up_Separation + 100 > Down_Separation)
  ensures Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) &
      (Climb_Inhibit = true)  & (Up_Separation + 100 > Down_Separation) &
  res = (!(Own_Tracked_Alt < Other_Tracked_Alt) | !(Down_Separation > a));

  // requires Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) &
  //     (Climb_Inhibit = false)  & (Up_Separation > Down_Separation)
  // ensures Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) &
  //     (Climb_Inhibit = false)  & (Up_Separation > Down_Separation) &
  // res = (!(Own_Tracked_Alt < Other_Tracked_Alt) | !(Down_Separation > a));

  // requires Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) &
  //     (Climb_Inhibit = true)  & (Up_Separation + 100 <= Down_Separation)
  // ensures Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) &
  //     (Climb_Inhibit = true)  & (Up_Separation + 100 <= Down_Separation) &
  // res = ((Cur_Vertical_Sep >= 300) & (Own_Tracked_Alt > Other_Tracked_Alt)
  //               & (Up_Separation >= a));

  // requires Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) &
  //     (Climb_Inhibit = false)  & (Up_Separation <= Down_Separation)
  // ensures Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) &
  //     (Climb_Inhibit = false)  & (Up_Separation <= Down_Separation) &
  // res = ((Cur_Vertical_Sep >= 300) & (Own_Tracked_Alt > Other_Tracked_Alt)
  //               & (Up_Separation >= a));


{
    bool result;

    if (Inhibit_Biased_Climb() > Down_Separation){
       result = (!Own_Below_Threat() ||
          (Own_Below_Threat() && !(Down_Separation > ALIM())));
    } else {	
       result = Own_Above_Threat() && (Cur_Vertical_Sep >= 300) && (Up_Separation >= ALIM());
    }
    return result;
}

bool Non_Crossing_Biased_Descend()
  requires Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) &
      (Climb_Inhibit = true)  & (Up_Separation + 100 > Down_Separation)
  ensures Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) &
      (Climb_Inhibit = true)  & (Up_Separation + 100 > Down_Separation) &
  res = ((Cur_Vertical_Sep >= 300) & (Other_Tracked_Alt > Own_Tracked_Alt)
                & (Down_Separation >= a));

  // requires Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) &
  //     (Climb_Inhibit = false)  & (Up_Separation > Down_Separation)
  // ensures Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) &
  //     (Climb_Inhibit = false)  & (Up_Separation > Down_Separation) &
  // res = ((Cur_Vertical_Sep >= 300) & (Other_Tracked_Alt > Own_Tracked_Alt)
  //               & (Down_Separation >= a));

  // requires Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) &
  //     (Climb_Inhibit = true)  & (Up_Separation + 100 <= Down_Separation)
  // ensures Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) &
  //     (Climb_Inhibit = true)  & (Up_Separation + 100 <= Down_Separation) &
  // res = (!(Own_Tracked_Alt > Other_Tracked_Alt) | (Up_Separation >= a));

  // requires Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) &
  //     (Climb_Inhibit = false)  & (Up_Separation <= Down_Separation)
  // ensures Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) &
  //     (Climb_Inhibit = false)  & (Up_Separation <= Down_Separation) &
  // res = (!(Own_Tracked_Alt > Other_Tracked_Alt) | (Up_Separation >= a));
{
    bool result;

    if (Inhibit_Biased_Climb() > Down_Separation){
     	result = Own_Below_Threat() && (Cur_Vertical_Sep >= 300) && (Down_Separation >= ALIM());
    } else   {
      result = !(Own_Above_Threat()) || ((Own_Above_Threat()) && (Up_Separation >= ALIM()));
    }
    return result;
}

int alt_sep_test()
  requires
  Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) &
      (Climb_Inhibit = true)  & (Up_Separation + 100 > Down_Separation)  &
      (Own_Tracked_Alt < Other_Tracked_Alt) & !(Down_Separation > a) &

  High_Confidence & (Own_Tracked_Alt_Rate <= 600) &
      (Cur_Vertical_Sep > 600) & ((Two_of_Three_Reports_Valid & Other_RAC = 0) |
      !(Other_Capability = 1))

  ensures
  Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) &
      (Climb_Inhibit = true)  & (Up_Separation + 100 > Down_Separation) &
      (Own_Tracked_Alt < Other_Tracked_Alt) & !(Down_Separation > a) &

  High_Confidence & (Own_Tracked_Alt_Rate <= 600) &
      (Cur_Vertical_Sep > 600) & ((Two_of_Three_Reports_Valid & Other_RAC = 0) |
      !(Other_Capability = 1))  &
  res = 1 ;

  

{
    bool enabled, tcas_equipped, intent_not_known;
    bool need_upward_RA, need_downward_RA;
    int alt_sep;
    alt_sep = 0;

    enabled = High_Confidence && (Own_Tracked_Alt_Rate <= 600) &&
      (Cur_Vertical_Sep > 600);
    tcas_equipped = Other_Capability == 1;
    intent_not_known = Two_of_Three_Reports_Valid && Other_RAC == 0;

    if (enabled && ((tcas_equipped && intent_not_known) || !tcas_equipped)){
      need_upward_RA = Non_Crossing_Biased_Climb() && Own_Below_Threat();
      need_downward_RA = Non_Crossing_Biased_Descend() && Own_Above_Threat();

      if (need_upward_RA && need_downward_RA)
	      alt_sep = 0;
	    else if (need_upward_RA)
	      alt_sep = 1;
	    else if (need_downward_RA)
	      alt_sep = 2;
	    else
	      alt_sep = 0;
    }

    return alt_sep;
}
