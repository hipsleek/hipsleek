
 WHAT IS THIS?
 =============
 This is a C++ implementation of AVL trees. The file DISCUSSION.txt in the
 parent directory contains a thorough discussion of AVL trees and their
 implementation. The files in this directory consist of source code and
 a test driver for an AVL tree class library written in C++. The parent
 directory contains a C implementation of AVL trees. Please note that
 this implementation is not particularly efficient: It uses recursion
 instead of iteration and imposes some extra levels of indirection.
 Efficiency was sacrificed in favor of making the code easy to learn from
 and to understand. Once you understand the code you can implement your
 own optimizations.


 VERSION
 =======
 This is *not* really a formal software package. The code is intended
 more for instructional use than for production use. I guess Ill call
 this release version 2.0.


 AUTHOR
 ======
 Brad Appleton <bradapp@enteract.com>


 COPY/REUSE POLICY
 =================
 Permission is hereby granted to freely copy and redistribute this
 software subject to the terms described in the file LICENSE.txt. Please
 read the file LICENSE.txt in this distribution for more details.


 DISCLAIMER
 ==========
 This software is provided ``As Is'' and without any express or implied
 warranties.  Neither the authors nor any of their employers (including
 any of their subsidiaries and subdivisions) are responsible for
 maintaining or supporting this software or for any consequences
 resulting from the use of this software, no matter how awful, even if
 they arise from flaws in the software. Please read the file LICENSE.txt
 in this distribution for more details.


 CONTENTS
 ========
 See the file "MANIFEST" in the distribution for a complete list and
 description of all the files included in this release.


 PORTING
 ============
 This software should compile on most platforms with a C++ compiler that
 supports templates. You may or may not experience difficulty depending
 on how well your C++ compiler supports templates. Also please look at
 the "Notes" near the beginning of Avl.h and Comparable.h regarding why
 the enum types cmp_t and dir_t are declared outside of their classes.
 If you find a "fix" for this please let me know.  You will need to
 modify the Makefile to configure which compiler and flags to use, and
 which directories to use.


 BUGS
 ====
 Please send all bug reports to the author.

