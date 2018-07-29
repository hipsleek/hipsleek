data node {
	int fst;
  int snd;
  int third;
  int fourth;
}

global int OLEV = 600;
global int MAXALTDIFF = 600;
global int MINSEP = 300;
global int NOZCROSS = 100;

global int Cur_Vertical_Sep;
global bool High_Confidence;
global bool Two_of_Three_Reports_Valid;

global int Own_Tracked_Alt;
global int Own_Tracked_Alt_Rate;
global int Other_Tracked_Alt;

global node Positive_RA_Alt_Thresh;
global int Alt_Layer_Value;

global int Up_Separation;
global int Down_Separation;

//state variables
global int Other_RAC;			// NO_INTENT, DO_NOT_CLIMB, DO_NOT_DESCEND
global int NO_INTENT = 0;
global int DO_NOT_CLIMB = 1;
global int DO_NOT_DESCEND = 2;

global int Other_Capability;		//TCAS_TA, OTHER
global int TCAS_TA = 1;
global int OTHER = 2;

global bool Climb_Inhibit;

global int UNRESOLVED = 0;
global int UPWARD_RA = 1;
global int DOWNWARD_RA = 2;

// error() when index is out of array bound
int int_error() requires true ensures false;

int ALIM()
  requires Positive_RA_Alt_Thresh::node<a, b, c, d> & Alt_Layer_Value = 0
  ensures Positive_RA_Alt_Thresh::node<a, b, c, d> & res = a;
  requires Positive_RA_Alt_Thresh::node<a, b, c, d> & Alt_Layer_Value = 1
  ensures Positive_RA_Alt_Thresh::node<a, b, c, d> & res = b;
  requires Positive_RA_Alt_Thresh::node<a, b, c, d> & Alt_Layer_Value = 2
  ensures Positive_RA_Alt_Thresh::node<a, b, c, d> & res = c;
  requires Positive_RA_Alt_Thresh::node<a, b, c, d> & Alt_Layer_Value = 3
  ensures Positive_RA_Alt_Thresh::node<a, b, c, d> & res = d;
  //requires Alt_Layer_Value < 0 | Alt_Layer_Value > 3 ensures false;
{
  if (Alt_Layer_Value == 0) return Positive_RA_Alt_Thresh.fst;
  if (Alt_Layer_Value == 1) return Positive_RA_Alt_Thresh.snd;
  if (Alt_Layer_Value == 2) return Positive_RA_Alt_Thresh.third;
  if (Alt_Layer_Value == 3) return Positive_RA_Alt_Thresh.fourth;
  return int_error();
}

int Inhibit_Biased_Climb ()
    requires Climb_Inhibit = true ensures res = Up_Separation + 100;
    requires Climb_Inhibit = false ensures res = Up_Separation;
{
    if (Climb_Inhibit) return Up_Separation + 100;
    return Up_Separation;
}

bool Own_Below_Threat()
  requires true ensures res = (Other_Tracked_Alt > Own_Tracked_Alt);
{
  return (Own_Tracked_Alt < Other_Tracked_Alt);
}

bool Own_Above_Threat()
     requires true ensures res = (Other_Tracked_Alt < Own_Tracked_Alt);
{
    return (Other_Tracked_Alt < Own_Tracked_Alt);
}

bool Non_Crossing_Biased_Climb()
 requires Positive_RA_Alt_Thresh::node<a, b, c, d> & (Alt_Layer_Value = 0) &
      (Climb_Inhibit = true)  & (Up_Separation + 100 > Down_Separation)
      ensures Positive_RA_Alt_Thresh::node<a, b, c, d> &
      res = ((Own_Tracked_Alt >= Other_Tracked_Alt) | (Down_Separation < a));
{
    bool result;
    bool upward_preferred;

    upward_preferred = Inhibit_Biased_Climb() > Down_Separation;
    if (upward_preferred) {
       result = !(Own_Below_Threat()) || (Down_Separation < ALIM());
    } else  {
      result = Own_Above_Threat() && (Cur_Vertical_Sep >= 300) && (Up_Separation >= ALIM());
    }
    return result;
}

bool Non_Crossing_Biased_Descend()
  requires Positive_RA_Alt_Thresh::node<a, b, c, d> & (Alt_Layer_Value = 0) &
      (Climb_Inhibit = true)  & (Up_Separation + 100 > Down_Separation)
  ensures Positive_RA_Alt_Thresh::node<a, b, c, d> &
  res = ((Cur_Vertical_Sep >= 300) & (Other_Tracked_Alt > Own_Tracked_Alt)
                & (Down_Separation >= a));  
{
    bool upward_preferred;
    bool result;

    upward_preferred = Inhibit_Biased_Climb() > Down_Separation;
    if (upward_preferred){
     	result = Own_Below_Threat() && (Cur_Vertical_Sep >= 300) && (Down_Separation >= ALIM());
    } else   {
      result = !(Own_Above_Threat()) || ((Own_Above_Threat()) && (Up_Separation >= ALIM()));
    }
    return result;
}

int alt_sep_test()
 requires Positive_RA_Alt_Thresh::node<a, b, c, d> & (Alt_Layer_Value = 0) &
      (Climb_Inhibit = true) & (Up_Separation + 100 > Down_Separation)
      & (Down_Separation < a)
  ensures res = 1;

{
    bool enabled, tcas_equipped, intent_not_known;
    bool need_upward_RA, need_downward_RA;
    int alt_sep;

    alt_sep = 0;
    need_downward_RA = Non_Crossing_Biased_Descend();
    need_upward_RA = Non_Crossing_Biased_Climb();
    if (need_downward_RA && need_upward_RA){
       return 4;
	  }
    if (need_upward_RA) return 1;
    if (need_downward_RA) return 2;
	  return alt_sep;
}

 // requires Positive_RA_Alt_Thresh::node<a, b, c, d> & Alt_Layer_Value = 1 &
 //      Climb_Inhibit = true  & Up_Separation + 100 > Down_Separation
 //      ensures res = ((Own_Tracked_Alt >= Other_Tracked_Alt) | (Down_Separation < b));
 // requires Positive_RA_Alt_Thresh::node<a, b, c, d> & Alt_Layer_Value = 2 &
 //      Climb_Inhibit = true  & Up_Separation + 100 > Down_Separation
 //      ensures res = ((Own_Tracked_Alt >= Other_Tracked_Alt) | (Down_Separation < c));
 // requires Positive_RA_Alt_Thresh::node<a, b, c, d> & Alt_Layer_Value = 3 &
 //      Climb_Inhibit = true  & Up_Separation + 100 > Down_Separation
 //      ensures res = ((Own_Tracked_Alt >= Other_Tracked_Alt) | (Down_Separation < d));
 // requires Positive_RA_Alt_Thresh::node<a, b, c, d> & Alt_Layer_Value = 0 &
 //       (Climb_Inhibit = false  & (Up_Separation > Down_Separation))
 //       ensures res = (Own_Tracked_Alt >= Other_Tracked_Alt) | (Down_Separation < a);
 // requires Positive_RA_Alt_Thresh::node<a, b, c, d> & Alt_Layer_Value = 1 &
 //       (Climb_Inhibit = false  & (Up_Separation > Down_Separation))
 //       ensures res = (Own_Tracked_Alt >= Other_Tracked_Alt) | (Down_Separation < b);
 // requires Positive_RA_Alt_Thresh::node<a, b, c, d> & Alt_Layer_Value = 2 &
 //       (Climb_Inhibit = false  & (Up_Separation > Down_Separation))
 //       ensures res = (Own_Tracked_Alt >= Other_Tracked_Alt) | (Down_Separation < c);
 // requires Positive_RA_Alt_Thresh::node<a, b, c, d> & Alt_Layer_Value = 3 &
 //       (Climb_Inhibit = false  & (Up_Separation > Down_Separation))
 //       ensures res = (Own_Tracked_Alt >= Other_Tracked_Alt) | (Down_Separation < d);

  // requires Positive_RA_Alt_Thresh::node<a, b, c, d> & Alt_Layer_Value = 0 &
  //     Climb_Inhibit = true  & Up_Separation + 100 <= Down_Separation
  //     ensures res = (Cur_Vertical_Sep >= 300 & Other_Tracked_Alt < Own_Tracked_Alt
  //       & Up_Separation >= a);
  // requires Positive_RA_Alt_Thresh::node<a, b, c, d> & Alt_Layer_Value = 1 &
  //     Climb_Inhibit = true  & Up_Separation + 100 <= Down_Separation
  //     ensures res = (Cur_Vertical_Sep >= 300 & Other_Tracked_Alt < Own_Tracked_Alt
  //       & Up_Separation >= b);
  // requires Positive_RA_Alt_Thresh::node<a, b, c, d> & Alt_Layer_Value = 2 &
  //     Climb_Inhibit = true  & Up_Separation + 100 <= Down_Separation
  //     ensures res = (Cur_Vertical_Sep >= 300 & Other_Tracked_Alt < Own_Tracked_Alt
  //       & Up_Separation >= c);
  // requires Positive_RA_Alt_Thresh::node<a, b, c, d> & Alt_Layer_Value = 3 &
  //     Climb_Inhibit = true  & Up_Separation + 100 <= Down_Separation
  //     ensures res = (Cur_Vertical_Sep >= 300 & Other_Tracked_Alt < Own_Tracked_Alt
  //       & Up_Separation >= d);

  // requires Positive_RA_Alt_Thresh::node<a, b, c, d> & Alt_Layer_Value = 0 &
  //       (Climb_Inhibit = false  & (Up_Separation <= Down_Separation))
  //    ensures res = ((Cur_Vertical_Sep >= 300) & (Other_Tracked_Alt < Own_Tracked_Alt)
  //       &(Up_Separation >= a));
  // requires Positive_RA_Alt_Thresh::node<a, b, c, d> & Alt_Layer_Value = 1 &
  //       (Climb_Inhibit = false  & (Up_Separation <= Down_Separation))
  //    ensures res = ((Cur_Vertical_Sep >= 300) & (Other_Tracked_Alt < Own_Tracked_Alt)
  //       &(Up_Separation >= b));
  // requires Positive_RA_Alt_Thresh::node<a, b, c, d> & Alt_Layer_Value = 2 &
  //       (Climb_Inhibit = false  & (Up_Separation <= Down_Separation))
  //    ensures res = ((Cur_Vertical_Sep >= 300) & (Other_Tracked_Alt < Own_Tracked_Alt)
  //       &(Up_Separation >= c));
  // requires Positive_RA_Alt_Thresh::node<a, b, c, d> & Alt_Layer_Value = 3 &
  //       (Climb_Inhibit = false  & (Up_Separation <= Down_Separation))
  //    ensures res = ((Cur_Vertical_Sep >= 300) & (Other_Tracked_Alt < Own_Tracked_Alt)
  //       &(Up_Separation >= d));
