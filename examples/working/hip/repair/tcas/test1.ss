data node {
	int fst;
}

global int OLEV = 600;
global int MAXALTDIFF = 600;
global int MINSEP = 300;
global int NOZCROSS = 100;
global int NO_INTENT = 0;
global int DO_NOT_CLIMB = 1;
global int DO_NOT_DESCEND = 2;
global int TCAS_TA = 1;
global int OTHER = 2;
global int UNRESOLVED = 0;
global int UPWARD_RA = 1;
global int DOWNWARD_RA = 2;

global int Cur_Vertical_Sep;
global bool High_Confidence;
global int Own_Tracked_Alt_Rate;
global int Own_Tracked_Alt;
global int Other_Tracked_Alt;
global node Positive_RA_Alt_Thresh;
global int Alt_Layer_Value;
global int Up_Separation;
global int Down_Separation;
global bool Two_of_Three_Reports_Valid;

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
    requires Climb_Inhibit = true
    ensures Climb_Inhibit = true & res = Up_Separation + NOZCROSS;
    requires Climb_Inhibit = false
    ensures Climb_Inhibit = false & res = Up_Separation;
{
    if (Climb_Inhibit) return Up_Separation + NOZCROSS;
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
requires Positive_RA_Alt_Thresh::node<a> & (Alt_Layer_Value = 0) &
      (Climb_Inhibit = true)  & (Up_Separation + NOZCROSS > Down_Separation)

ensures Positive_RA_Alt_Thresh::node<a> & (Alt_Layer_Value = 0)
      & (Climb_Inhibit = true)  & (Up_Separation + NOZCROSS > Down_Separation)
       & res = (((Own_Tracked_Alt >= Other_Tracked_Alt)) | (Down_Separation < a));

requires Positive_RA_Alt_Thresh::node<a> & (Alt_Layer_Value = 0) &
      (Climb_Inhibit = true)  & (Up_Separation + NOZCROSS <= Down_Separation)

ensures Positive_RA_Alt_Thresh::node<a> & (Alt_Layer_Value = 0)
   & (Climb_Inhibit = true)  & (Up_Separation + NOZCROSS <= Down_Separation)
   & res = (Own_Tracked_Alt > Other_Tracked_Alt & Cur_Vertical_Sep >= MINSEP & Up_Separation >= a);

{
    bool result;
    bool upward_preferred;

    upward_preferred = Inhibit_Biased_Climb() > Down_Separation;
    if (upward_preferred) {
       result = (!(Own_Below_Threat()) || (Down_Separation < ALIM()) );
    } else  {
      result = Own_Above_Threat() && (Cur_Vertical_Sep >= MINSEP) && (Up_Separation >= ALIM());
    }
    return result;
}

bool Non_Crossing_Biased_Descend()
requires Positive_RA_Alt_Thresh::node<a> & (Alt_Layer_Value = 0) &
      (Climb_Inhibit = true)  & (Up_Separation + NOZCROSS > Down_Separation)

ensures Positive_RA_Alt_Thresh::node<a> & (Alt_Layer_Value = 0)
 & (Climb_Inhibit = true)  & (Up_Separation + NOZCROSS > Down_Separation)
 & res = (Own_Tracked_Alt < Other_Tracked_Alt & Cur_Vertical_Sep >= MINSEP & Down_Separation >= a);

requires Positive_RA_Alt_Thresh::node<a> & (Alt_Layer_Value = 0) &
      (Climb_Inhibit = true)  & (Up_Separation + NOZCROSS <= Down_Separation)

ensures Positive_RA_Alt_Thresh::node<a> & (Alt_Layer_Value = 0)
      & (Climb_Inhibit = true)  & (Up_Separation + NOZCROSS <= Down_Separation)
      & res = ( (Own_Tracked_Alt <= Other_Tracked_Alt) | (Up_Separation >= a));

{
    bool upward_preferred;
    bool result;

    upward_preferred = Inhibit_Biased_Climb() > Down_Separation;
    if (upward_preferred) {
       result = Own_Below_Threat() && (Cur_Vertical_Sep >= MINSEP) && (Down_Separation >= ALIM());
    }  else  {
	     result = !(Own_Above_Threat()) || (Up_Separation >= ALIM());
    }
    return result;
}

int alt_sep_test()
requires Positive_RA_Alt_Thresh::node<a>
   & High_Confidence & (Own_Tracked_Alt_Rate <= OLEV) & (Cur_Vertical_Sep > MAXALTDIFF)
   & ((Two_of_Three_Reports_Valid & Other_RAC = NO_INTENT) | !(Other_Capability = TCAS_TA))
   & (Climb_Inhibit = true)  & (Up_Separation + NOZCROSS <= Down_Separation)
   & (Alt_Layer_Value = 0)
   & (Own_Tracked_Alt > Other_Tracked_Alt) & (Up_Separation >= a)
   
ensures Positive_RA_Alt_Thresh::node<a>
   & High_Confidence & (Own_Tracked_Alt_Rate <= OLEV) & (Cur_Vertical_Sep > MAXALTDIFF)
   & ((Two_of_Three_Reports_Valid & Other_RAC = NO_INTENT) | !(Other_Capability = TCAS_TA))
   &  (Climb_Inhibit = true)  & (Up_Separation + NOZCROSS <= Down_Separation)
   & (Alt_Layer_Value = 0)
   & (Own_Tracked_Alt > Other_Tracked_Alt) & (Up_Separation >= a)
   & res = DOWNWARD_RA;

requires Positive_RA_Alt_Thresh::node<a> 
   & High_Confidence & (Own_Tracked_Alt_Rate <= OLEV) & (Cur_Vertical_Sep > MAXALTDIFF)
   & ((Two_of_Three_Reports_Valid & Other_RAC = NO_INTENT) | !(Other_Capability = TCAS_TA))
   & (Alt_Layer_Value = 0)
   & (Climb_Inhibit = true)  & (Up_Separation + NOZCROSS > Down_Separation)
   & (Own_Tracked_Alt < Other_Tracked_Alt) & (Down_Separation < a)

ensures Positive_RA_Alt_Thresh::node<a> 
   & High_Confidence & (Own_Tracked_Alt_Rate <= OLEV) & (Cur_Vertical_Sep > MAXALTDIFF)
   & ((Two_of_Three_Reports_Valid & Other_RAC = NO_INTENT) | !(Other_Capability = TCAS_TA))
   & (Alt_Layer_Value = 0)
   & (Climb_Inhibit = true)  & (Up_Separation + NOZCROSS > Down_Separation)
   & (Own_Tracked_Alt < Other_Tracked_Alt) & (Down_Separation < a)
   & res = UPWARD_RA;

{
  bool enabled, tcas_equipped, intent_not_known;
  bool need_upward_RA, need_downward_RA;
  int alt_sep;

  alt_sep = UNRESOLVED;
  enabled = High_Confidence && (Own_Tracked_Alt_Rate <= OLEV) && (Cur_Vertical_Sep > MAXALTDIFF);
  tcas_equipped = Other_Capability == TCAS_TA;
  intent_not_known = Two_of_Three_Reports_Valid && Other_RAC == NO_INTENT;
  need_upward_RA = Non_Crossing_Biased_Climb() && Own_Below_Threat();
  need_downward_RA = Non_Crossing_Biased_Descend() && Own_Above_Threat();

  if (enabled && ((tcas_equipped && intent_not_known) || !tcas_equipped)){
       if (need_upward_RA && need_downward_RA)	    alt_sep = UNRESOLVED;
	     else if (need_upward_RA)	    alt_sep = UPWARD_RA;
	     else if (need_downward_RA)   alt_sep = DOWNWARD_RA;
	     else	    alt_sep = UNRESOLVED;
   }
    return alt_sep;
}
