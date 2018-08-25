#include <stdbool.h>
struct node {
	int fst;
  int snd;
  int third;
  int fourth;
};

#define OLEV       600		/* in feets/minute */
#define MAXALTDIFF 600		/* max altitude difference in feet */
#define MINSEP     300          /* min separation in feet */
#define NOZCROSS   100		/* in feet */
#define NO_INTENT 0
#define DO_NOT_CLIMB 1
#define DO_NOT_DESCEND 2
#define TCAS_TA 1
#define OTHER 2
#define UNRESOLVED 0
#define UPWARD_RA 1
#define DOWNWARD_RA 2

/* typedef int bool; */
/* #define true 1 */
/* #define false 0 */

struct node Positive_RA_Alt_Thresh;
int Alt_Layer_Value;		/* 0, 1, 2, 3 */

int Cur_Vertical_Sep;
bool High_Confidence;
bool Two_of_Three_Reports_Valid;

int Own_Tracked_Alt;
int Own_Tracked_Alt_Rate;
int Other_Tracked_Alt;

int Up_Separation;
int Down_Separation;

int Other_RAC;			/* NO_INTENT, DO_NOT_CLIMB, DO_NOT_DESCEND */
int Other_Capability;		/* TCAS_TA, OTHER */

int Climb_Inhibit;		/* true/false */

// error() when index is out of array bound
int int_error()
/*@requires true ensures false;*/
{}

void initialize()
/*@
  requires Positive_RA_Alt_Thresh::node<a,b,c,d>
  ensures Positive_RA_Alt_Thresh::node<a2,b2,c2,d2> &
  a2 = 400 & b2 = 500 & c2 = 640 & d2 = 740;
*/
{
  Positive_RA_Alt_Thresh.fst = 400;
  Positive_RA_Alt_Thresh.snd = 500;
  Positive_RA_Alt_Thresh.third = 640;
  Positive_RA_Alt_Thresh.fourth = 740;
}

int ALIM()
/*@
  requires Positive_RA_Alt_Thresh::node<a,b,c,d> & Alt_Layer_Value = 0
  ensures Positive_RA_Alt_Thresh::node<a,b,c,d> & Alt_Layer_Value = 0 & res = a;
  requires Positive_RA_Alt_Thresh::node<a,b,c,d> & Alt_Layer_Value = 1
  ensures Positive_RA_Alt_Thresh::node<a,b,c,d> & Alt_Layer_Value = 1 & res = b;
*/
{
  if (Alt_Layer_Value == 0) return Positive_RA_Alt_Thresh.fst;
  if (Alt_Layer_Value == 1) return Positive_RA_Alt_Thresh.snd;
  return int_error();
}

int Inhibit_Biased_Climb ()
/*@
  requires Climb_Inhibit = 1
  ensures Climb_Inhibit = 1 & res = Up_Separation + 100;
  requires Climb_Inhibit = 0
  ensures Climb_Inhibit = 0 & res = Up_Separation;
 */
{
  if (Climb_Inhibit) {
    return Up_Separation + NOZCROSS;
  } else {
    return Up_Separation;
  }
}

bool Own_Above_Threat()
/*@
  requires true ensures res = (Other_Tracked_Alt < Own_Tracked_Alt);
 */
{
  return (Other_Tracked_Alt < Own_Tracked_Alt);
}

bool Own_Below_Threat()
/*@
  requires true ensures res = (Other_Tracked_Alt > Own_Tracked_Alt);
*/
{
  return (Own_Tracked_Alt < Other_Tracked_Alt);
}

bool Non_Crossing_Biased_Climb()
/*@
  requires Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) &
  (Climb_Inhibit = 1)  & (Up_Separation + 100 > Down_Separation)

  ensures Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0)
  & (Climb_Inhibit = 1)  & (Up_Separation + 100 > Down_Separation)
  & res = (((Own_Tracked_Alt >= Other_Tracked_Alt)) | (Down_Separation < a));

  requires Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) &
  (Climb_Inhibit = 1)  & (Up_Separation + 100 <= Down_Separation)

  ensures Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0)
  & (Climb_Inhibit = 1)  & (Up_Separation + 100 <= Down_Separation)
  & res = (Own_Tracked_Alt > Other_Tracked_Alt & Cur_Vertical_Sep >= 300 & Up_Separation >= a);
 */
{
  bool upward_preferred;
  bool result;

  //  upward_preferred = Inhibit_Biased_Climb() > Down_Separation;
  if (Inhibit_Biased_Climb() > Down_Separation){
    // >= -> >
    result = !(Own_Below_Threat()) || ((Own_Below_Threat()) && (!(Down_Separation > ALIM())));
  } else {
    result = Own_Above_Threat() && (Cur_Vertical_Sep >= MINSEP) && (Up_Separation >= ALIM());
  }

  return result;
}

/* bool Non_Crossing_Biased_Descend() */
/* /\*@ */
/*   requires Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) & */
/*   (Climb_Inhibit = 1)  & (Up_Separation + 100 > Down_Separation) */

/*   ensures Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) */
/*   & (Climb_Inhibit = 1)  & (Up_Separation + 100 > Down_Separation) */
/*   & res = (Own_Tracked_Alt < Other_Tracked_Alt & Cur_Vertical_Sep >= 300 & Down_Separation >= a); */

/*   requires Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) & */
/*   (Climb_Inhibit = 1)  & (Up_Separation + 100 <= Down_Separation) */

/*   ensures Positive_RA_Alt_Thresh::node<a,b,c,d> & (Alt_Layer_Value = 0) */
/*   & (Climb_Inhibit = 1)  & (Up_Separation + 100 <= Down_Separation) */
/*   & res = ( (Own_Tracked_Alt <= Other_Tracked_Alt) | (Up_Separation >= a)); */
/*  *\/ */
/* { */
/*   bool upward_preferred; */
/*   bool result; */

/*   //upward_preferred = Inhibit_Biased_Climb() > Down_Separation; */
/*   if (Inhibit_Biased_Climb() > Down_Separation){ */
/*     result = Own_Below_Threat() && (Cur_Vertical_Sep >= MINSEP) && (Down_Separation >= ALIM()); */
/*   } else { */
/*     result = !(Own_Above_Threat()) || ((Own_Above_Threat()) && (Up_Separation >= ALIM())); */
/*   } */
/*   return result; */
/* } */

/* int alt_sep_test() */
/* /\*@ */
/* requires Positive_RA_Alt_Thresh::node<a,b,c,d> */
/*    & High_Confidence & (Own_Tracked_Alt_Rate <= 600) & (Cur_Vertical_Sep > 600) */
/*    & ((Two_of_Three_Reports_Valid & Other_RAC = 0) | !(Other_Capability = 1)) */
/*    & (Climb_Inhibit = 1)  & (Up_Separation + 100 <= Down_Separation) */
/*    & (Alt_Layer_Value = 0) */
/*    & (Own_Tracked_Alt > Other_Tracked_Alt) & (Up_Separation >= a) */

/* ensures Positive_RA_Alt_Thresh::node<a,b,c,d> */
/*    & High_Confidence & (Own_Tracked_Alt_Rate <= 600) & (Cur_Vertical_Sep > 600) */
/*    & ((Two_of_Three_Reports_Valid & Other_RAC = 0) | !(Other_Capability = 1)) */
/*    &  (Climb_Inhibit = 1)  & (Up_Separation + 100 <= Down_Separation) */
/*    & (Alt_Layer_Value = 0) */
/*    & (Own_Tracked_Alt > Other_Tracked_Alt) & (Up_Separation >= a) */
/*    & res = 2; */

/* requires Positive_RA_Alt_Thresh::node<a,b,c,d> */
/*    & High_Confidence & (Own_Tracked_Alt_Rate <= 600) & (Cur_Vertical_Sep > 600) */
/*    & ((Two_of_Three_Reports_Valid & Other_RAC = 0) | !(Other_Capability = 1)) */
/*    & (Climb_Inhibit = 1)  & (Up_Separation + 100 > Down_Separation) */
/*    & (Alt_Layer_Value = 0) */
/*    & (Own_Tracked_Alt < Other_Tracked_Alt) & (Down_Separation < a) */

/* ensures Positive_RA_Alt_Thresh::node<a,b,c,d> */
/*    & High_Confidence & (Own_Tracked_Alt_Rate <= 600) & (Cur_Vertical_Sep > 600) */
/*    & ((Two_of_Three_Reports_Valid & Other_RAC = 0) | !(Other_Capability = 1)) */
/*    & (Climb_Inhibit = 1)  & (Up_Separation + 100 > Down_Separation) */
/*    & (Alt_Layer_Value = 0) */
/*    & (Own_Tracked_Alt < Other_Tracked_Alt) & (Down_Separation < a) */
/*    & res = 1; */
/* *\/ */
/* { */
/*   bool enabled, tcas_equipped, intent_not_known; */
/*   bool need_upward_RA, need_downward_RA; */
/*   int alt_sep; */

/*   alt_sep = UNRESOLVED; */
/*   enabled = High_Confidence && (Own_Tracked_Alt_Rate <= OLEV) && (Cur_Vertical_Sep > MAXALTDIFF); */
/*   tcas_equipped = Other_Capability == TCAS_TA; */
/*   intent_not_known = Two_of_Three_Reports_Valid && Other_RAC == NO_INTENT; */

/*   need_upward_RA = Non_Crossing_Biased_Climb() && Own_Below_Threat(); */
/*   need_downward_RA = Non_Crossing_Biased_Descend() && Own_Above_Threat(); */

/*   if (enabled && ((tcas_equipped && intent_not_known) || !tcas_equipped)){ */
/*        if (need_upward_RA && need_downward_RA)	    alt_sep = UNRESOLVED; */
/* 	     else if (need_upward_RA)	    alt_sep = UPWARD_RA; */
/* 	     else if (need_downward_RA)   alt_sep = DOWNWARD_RA; */
/* 	     else	    alt_sep = UNRESOLVED; */
/*   } */
/*   return alt_sep; */
/* } */


