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
  if (Alt_Layer_Value == 2) return Positive_RA_Alt_Thresh.third;
  if (Alt_Layer_Value == 3) return Positive_RA_Alt_Thresh.fourth;
  return int_error();
}

