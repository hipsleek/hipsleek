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

bool Climb_Inhibit;		/* true/false */

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
  Positive_RA_Alt_Thresh.fourth = 700;
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
  requires Climb_Inhibit = true
  ensures Climb_Inhibit = true & res = Up_Separation + 100;
  requires Climb_Inhibit = false
  ensures Climb_Inhibit = false & res = Up_Separation;
 */
{
  return (Climb_Inhibit ? Up_Separation + NOZCROSS : Up_Separation);
}

bool Own_Below_Threat()
/*@
  requires true ensures res = (Other_Tracked_Alt > Own_Tracked_Alt);
*/
{
  return (Own_Tracked_Alt < Other_Tracked_Alt);
}

