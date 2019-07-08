/* $Id: notedd.h,v 1.1 2010-12-10 07:42:12 locle Exp $ */
#ifndef Already_Included_NoteDD
#define Already_Included_NoteDD

namespace omega {

/* information about nodes involved in dependence */
struct situation{
    a_access access1, access2;
    ddnature oitype, iotype;
    unsigned int nest1, nest2, commonNesting;
};

void noteDependence(situation *sit, dir_and_diff_info *d_info);
void keep_dependence(situation *sit, dir_and_diff_info *d_info);

}

#endif

