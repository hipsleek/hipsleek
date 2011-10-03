
/*  -*- Last-Edit:  Fri Jan 29 11:13:27 1993 by Tarak S. Goradia; -*- */
/* $Log: tcas.c,v $
 * Revision 1.2  1993/03/12  19:29:50  foster
 * Correct logic bug which didn't allow output of 2 - hf
 * */

//#include <stdio.h>
relation dom(int[] a, int x, int y) == true.


//#define OLEV       600		/* in feets/minute */
//#define MAXALTDIFF 600		/* max altitude difference in feet */
//#define MINSEP     300          /* min separation in feet */
//#define NOZCROSS   100		/* in feet */
				/* variables */

//typedef int bool;

global int Cur_Vertical_Sep;
global bool High_Confidence;
global bool Two_of_Three_Reports_Valid;

global int Own_Tracked_Alt;
global int Own_Tracked_Alt_Rate;
global int Other_Tracked_Alt;

global int Alt_Layer_Value;		/* 0, 1, 2, 3 */
//int Positive_RA_Alt_Thresh[4];

global int Up_Separation;
global int Down_Separation;

				/* state variables */
global int Other_RAC;			/* NO_INTENT, DO_NOT_CLIMB, DO_NOT_DESCEND */
//#define NO_INTENT 0
//#define DO_NOT_CLIMB 1
//#define DO_NOT_DESCEND 2

global int Other_Capability;		/* TCAS_TA, OTHER */
//#define TCAS_TA 1
//#define OTHER 2

global bool Climb_Inhibit;		/* true/false */

//#define UNRESOLVED 0
//#define UPWARD_RA 1
//#define DOWNWARD_RA 2

void initialize(ref int[] Positive_RA_Alt_Thresh)
    requires  dom(Positive_RA_Alt_Thresh, 0, 3)
    ensures  dom(Positive_RA_Alt_Thresh', 0, 3) & Positive_RA_Alt_Thresh'[0] = 400 &  Positive_RA_Alt_Thresh'[1] = 500 &
                 Positive_RA_Alt_Thresh'[2] = 640 &  Positive_RA_Alt_Thresh'[3] = 740;
{
    Positive_RA_Alt_Thresh[0] = 400;
    Positive_RA_Alt_Thresh[1] = 500;
    Positive_RA_Alt_Thresh[2] = 640;
    Positive_RA_Alt_Thresh[3] = 740;
}

int ALIM (int i, ref int[] Positive_RA_Alt_Thresh)
    requires  dom(Positive_RA_Alt_Thresh, 0, 3) &  Positive_RA_Alt_Thresh[0] = 400 &  Positive_RA_Alt_Thresh[1] = 500 &
                 Positive_RA_Alt_Thresh[2] = 640 &  Positive_RA_Alt_Thresh[3] = 740 &
                 i = 0
    ensures  dom(Positive_RA_Alt_Thresh', 0, 3)  &  Positive_RA_Alt_Thresh'[0] = 400 &  Positive_RA_Alt_Thresh'[1] = 500 &
                 Positive_RA_Alt_Thresh'[2] = 640 &  Positive_RA_Alt_Thresh'[3] = 740  &
     (res = 400);
//(res = 400 | res = 500 | res = 640 | res = 740)
{
 return Positive_RA_Alt_Thresh[i];
}

/*
case {
    Climb_Inhibit -> ensures res= (Up_Separation+100);
    !Climb_Inhibit -> ensures res= Up_Separation;
}
*/

int Inhibit_Biased_Climb ()
  requires !Climb_Inhibit
  ensures res = Up_Separation & Up_Separation' = Up_Separation & !Climb_Inhibit';
{
  if (Climb_Inhibit) return (Up_Separation + 100);
	else return Up_Separation;
//    return (Climb_Inhibit ? Up_Separation + 100 : Up_Separation);
}

bool Non_Crossing_Biased_Climb(ref int[] Positive_RA_Alt_Thresh)
   requires  dom(Positive_RA_Alt_Thresh, 0, 3) & Positive_RA_Alt_Thresh[0] = 400 &  Positive_RA_Alt_Thresh[1] = 500 &
             Positive_RA_Alt_Thresh[2] = 640 &  Positive_RA_Alt_Thresh[3] = 740 & (Alt_Layer_Value = 0)  &
             !Climb_Inhibit & (Cur_Vertical_Sep > 600) &
            (Up_Separation < Down_Separation)
   case {
     Other_Tracked_Alt < Own_Tracked_Alt ->
       case {
         Up_Separation >= 400 ->
           ensures dom(Positive_RA_Alt_Thresh', 0, 3) & Positive_RA_Alt_Thresh'[0] = 400 &  Positive_RA_Alt_Thresh'[1] = 500 &
              Positive_RA_Alt_Thresh'[2] = 640 &  Positive_RA_Alt_Thresh'[3] = 740 &
             (Alt_Layer_Value' = 0) & !Climb_Inhibit' & (Cur_Vertical_Sep' > 600) &
             (Up_Separation' = Up_Separation &  Down_Separation'=Down_Separation) &
             res;
         Up_Separation < 400 ->
           ensures dom(Positive_RA_Alt_Thresh', 0, 3) & Positive_RA_Alt_Thresh'[0] = 400 &  Positive_RA_Alt_Thresh'[1] = 500 &
              Positive_RA_Alt_Thresh'[2] = 640 &  Positive_RA_Alt_Thresh'[3] = 740 &
             (Alt_Layer_Value' = Alt_Layer_Value) & Climb_Inhibit'= Climb_Inhibit  & (Cur_Vertical_Sep' = Cur_Vertical_Sep) &
             (Up_Separation' = Up_Separation &  Down_Separation'=Down_Separation) &
             !res;
       }
     Other_Tracked_Alt >= Own_Tracked_Alt ->
          ensures dom(Positive_RA_Alt_Thresh', 0, 3) & Positive_RA_Alt_Thresh'[0] = 400 &  Positive_RA_Alt_Thresh'[1] = 500 &
              Positive_RA_Alt_Thresh'[2] = 640 &  Positive_RA_Alt_Thresh'[3] = 740 &
              (Alt_Layer_Value' = Alt_Layer_Value) & Climb_Inhibit'= Climb_Inhibit  & (Cur_Vertical_Sep' = Cur_Vertical_Sep) &
             (Up_Separation' = Up_Separation &  Down_Separation'=Down_Separation) &
             !res;
   }
{
    bool upward_preferred;
    int upward_crossing_situation;
    bool result;

    upward_preferred = Inhibit_Biased_Climb() > Down_Separation;
    if (upward_preferred)
    {
      result = !(Own_Below_Threat()) || ((Own_Below_Threat()) &&
           (!(Down_Separation >= ALIM(Alt_Layer_Value, Positive_RA_Alt_Thresh))));
    }
    else
    {
      result = Own_Above_Threat() && (Cur_Vertical_Sep >= 300) &&
            (Up_Separation >= ALIM(Alt_Layer_Value, Positive_RA_Alt_Thresh));
    }
    return result;
}

bool Non_Crossing_Biased_Descend(ref int[] Positive_RA_Alt_Thresh)
   requires dom(Positive_RA_Alt_Thresh, 0, 3) & Positive_RA_Alt_Thresh[0] = 400 &  Positive_RA_Alt_Thresh[1] = 500 &
                 Positive_RA_Alt_Thresh[2] = 640 &  Positive_RA_Alt_Thresh[3] = 740 &
   (Alt_Layer_Value = 0) & !Climb_Inhibit & (Up_Separation < Down_Separation)
    case {
       Other_Tracked_Alt < Own_Tracked_Alt->
       case {
         Up_Separation >= 400 -> ensures dom(Positive_RA_Alt_Thresh', 0, 3) & Positive_RA_Alt_Thresh'[0] = 400 &  Positive_RA_Alt_Thresh'[1] = 500 & Positive_RA_Alt_Thresh'[2] = 640 &  Positive_RA_Alt_Thresh'[3] = 740 &
                                res ;
         Up_Separation < 400 ->
           ensures dom(Positive_RA_Alt_Thresh', 0, 3) & Positive_RA_Alt_Thresh'[0] = 400 &  Positive_RA_Alt_Thresh'[1] = 500 & Positive_RA_Alt_Thresh'[2] = 640 &  Positive_RA_Alt_Thresh'[3] = 740 &
                      !res ;
       }
       Other_Tracked_Alt >= Own_Tracked_Alt ->
          ensures dom(Positive_RA_Alt_Thresh', 0, 3) & Positive_RA_Alt_Thresh'[0] = 400 &  Positive_RA_Alt_Thresh'[1] = 500 & Positive_RA_Alt_Thresh'[2] = 640 &  Positive_RA_Alt_Thresh'[3] = 740 &
                      res;
   }
{
    bool locupward_preferred;
    int upward_crossing_situation;
    bool result;
    bool temp1;
	int temp2;
/*
    int temp;
    temp = Inhibit_Biased_Climb();
    if (temp > Down_Separation) {upward_preferred = true;}
    else {upward_preferred = false;}
*/
    locupward_preferred = Inhibit_Biased_Climb() > Down_Separation;
    if (locupward_preferred)
    {
      result = Own_Below_Threat() && (Cur_Vertical_Sep >= 300) && (Down_Separation >= ALIM(Alt_Layer_Value, Positive_RA_Alt_Thresh));
    }
    else
    {
    temp1 = Own_Above_Threat();
	temp2 = ALIM(Alt_Layer_Value, Positive_RA_Alt_Thresh);
	result = 
	!(temp1) || 
	((temp1) && 
	(Up_Separation >= temp2));
    }
    return result;
}

bool Own_Below_Threat()
   case {
   Own_Tracked_Alt < Other_Tracked_Alt ->
         ensures res & Other_Tracked_Alt'=Other_Tracked_Alt & Own_Tracked_Alt'=Own_Tracked_Alt ;
   Own_Tracked_Alt >= Other_Tracked_Alt ->
         ensures !res & Other_Tracked_Alt'=Other_Tracked_Alt & Own_Tracked_Alt'=Own_Tracked_Alt;
   }
{
    return (Own_Tracked_Alt < Other_Tracked_Alt);
}

bool Own_Above_Threat()
case {
   Other_Tracked_Alt < Own_Tracked_Alt ->
      ensures res & Other_Tracked_Alt'=Other_Tracked_Alt & Own_Tracked_Alt'=Own_Tracked_Alt;
   Other_Tracked_Alt >= Own_Tracked_Alt ->
      ensures !res & Other_Tracked_Alt'=Other_Tracked_Alt & Own_Tracked_Alt'=Own_Tracked_Alt;
   }
{
    return (Other_Tracked_Alt < Own_Tracked_Alt);
}

int alt_sep_test(ref int[] Positive_RA_Alt_Thresh)
    requires  dom(Positive_RA_Alt_Thresh, 0, 3) & Positive_RA_Alt_Thresh[0] = 400 &  Positive_RA_Alt_Thresh[1] = 500 &
                 Positive_RA_Alt_Thresh[2] = 640 &  Positive_RA_Alt_Thresh[3] = 740 &
  (Alt_Layer_Value = 0) & Own_Tracked_Alt_Rate <= 600 &
  (Other_Capability = 0) & !Climb_Inhibit & High_Confidence & (Cur_Vertical_Sep > 600) &
   (Up_Separation < Down_Separation)
    ensures  ( res=0 | res=2 | res=3| res=1);
{
    bool enabled, tcas_equipped, intent_not_known;
    bool need_upward_RA, need_downward_RA;
    int alt_sep;

    enabled = High_Confidence && (Own_Tracked_Alt_Rate <= 600) && (Cur_Vertical_Sep > 600);
    tcas_equipped = Other_Capability == 1;
    intent_not_known = Two_of_Three_Reports_Valid && Other_RAC == 0;
    
    alt_sep = 4;
    
    if (enabled && ((tcas_equipped && intent_not_known) || !tcas_equipped))
    {
	need_upward_RA = Non_Crossing_Biased_Climb(Positive_RA_Alt_Thresh) && Own_Below_Threat();
	need_downward_RA = Non_Crossing_Biased_Descend(Positive_RA_Alt_Thresh) && Own_Above_Threat();
	if (need_upward_RA && need_downward_RA)
        /* unreachable: requires Own_Below_Threat and Own_Above_Threat
           to both be true - that requires Own_Tracked_Alt < Other_Tracked_Alt
           and Other_Tracked_Alt < Own_Tracked_Alt, which isn't possible */
	    alt_sep = 3;
	else if (need_upward_RA)
	    alt_sep = 1;
	else if (need_downward_RA)
	    alt_sep = 2;
	else
	    alt_sep = 0;
    }
    
    return alt_sep;
}

int main(int argc, /*argv,*/ ref int[] Positive_RA_Alt_Thresh)
	requires  dom(Positive_RA_Alt_Thresh, 0, 3)
  ensures  true;
//int argc;
//char *argv[];
{
    if(argc < 13)
    { /*
	fprintf(stdout, "Error: Command line arguments are\n");
	fprintf(stdout, "Cur_Vertical_Sep, High_Confidence, Two_of_Three_Reports_Valid\n");
	fprintf(stdout, "Own_Tracked_Alt, Own_Tracked_Alt_Rate, Other_Tracked_Alt\n");
	fprintf(stdout, "Alt_Layer_Value, Up_Separation, Down_Separation\n");
	fprintf(stdout, "Other_RAC, Other_Capability, Climb_Inhibit\n");
	exit(1);
	*/
	return 1;
    }
    initialize(Positive_RA_Alt_Thresh);
	/*
    Cur_Vertical_Sep = atoi(argv[1]);
    High_Confidence = atoi(argv[2]);
    Two_of_Three_Reports_Valid = atoi(argv[3]);
    Own_Tracked_Alt = atoi(argv[4]);
    Own_Tracked_Alt_Rate = atoi(argv[5]);
    Other_Tracked_Alt = atoi(argv[6]);
    Alt_Layer_Value = atoi(argv[7]);
    Up_Separation = atoi(argv[8]);
    Down_Separation = atoi(argv[9]);
    Other_RAC = atoi(argv[10]);
    Other_Capability = atoi(argv[11]);
    Climb_Inhibit = atoi(argv[12]);
    */
    //fprintf(stdout, "%d\n", alt_sep_test());
    assume(Alt_Layer_Value = 0);
    //  tcas_equipped = false
    assume(Other_Capability = 0);
    assume(!Climb_Inhibit);
    //make sure enable
    assume(High_Confidence);
    assume (Cur_Vertical_Sep > 600);
    assume ( Own_Tracked_Alt_Rate <= 600);
    assume (Up_Separation < Down_Separation);
	alt_sep_test();
    //exit(0);
	return 0;
}
