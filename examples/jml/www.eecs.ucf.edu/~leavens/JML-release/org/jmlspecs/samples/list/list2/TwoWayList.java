// @(#) $Id: TwoWayList.java,v 1.2 2009-02-17 08:55:21 chinwn Exp $

// Copyright (C) 1998, 1999 Iowa State University

// This file is part of JML

// JML is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2, or (at your option)
// any later version.

// JML is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with JML; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

// Author:  Clyde Ruby

package org.jmlspecs.samples.list.list2;

//@ refine "TwoWayList.jml";

import org.jmlspecs.samples.list.node.TwoWayNode;

// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public class TwoWayList extends E_OneWayList { // Doubly Linked List

    protected TwoWayNode lastNode_;

    public TwoWayList() {
	theListNode_ = new TwoWayNode(null);
	length_ = 0;

	// The next statements are needed to satisfy the class invariant!!!
	// model field 'cursor' needs a valid value before the call!
	cursorNode_ = theListNode_;
	lastNode_ = (TwoWayNode) theListNode_;

	firstEntry();
    }
    // iteration methods
    // -----------------

    // NEW iteration methods (for doubly linked list)
    // ---------------------
    public void decrementCursor() {
	if (isOffFront()) {
	    // System.err.println("Error in `list2.TwoWayList.decrementCursor': cursorNode_ is invalid");
	    throw new IllegalStateException("Error in `list2.TwoWayList.decrementCursor': cursorNode_ is invalid");
	}
	if (isOffEnd()) {
	    lastEntry();
	} else {
	    cursorNode_ = ((TwoWayNode)cursorNode_).getPrevNode();
	}
    }
    public void lastEntry() {
	cursorNode_ = lastNode_;
    }
    public void removeEntry() {
	if (isOffEnd() || isOffFront()) {
	    // System.err.println("Error in `list2.TwoWayList.removeEntry': cursorNode_ is invalid\n"
	    //	       + "List is " + this.toString() );
	    throw new IllegalStateException("Error in `list2.TwoWayList.removeEntry': cursorNode_ is invalid\n"
					    + "List is " + this.toString() );
	}

	decrementCursor();

	if (cursorNode_.getNextNode() == lastNode_) {
	    lastNode_ = (TwoWayNode) cursorNode_;
	}

	cursorNode_.removeNextNode();
	length_ --;
    }
    public void insertAfterCursor(Object newEntry) {
	if ( isOffEnd() ) {
	    decrementCursor();
	    cursorNode_.insertAfter(newEntry);
	    incrementCursor();
	    lastNode_ = (TwoWayNode) cursorNode_;
	    incrementCursor();
	    length_ ++;
	} else {
	    super.insertAfterCursor(newEntry);
	    // cursorNode_.insertAfter(newEntry);
	    // length_ ++;
	    if (lastNode_ == cursorNode_) {
		lastNode_ = (TwoWayNode) cursorNode_.getNextNode();
	    }
	}
    }
    public void insertBeforeCursor(Object newEntry) {
	if ( isOffFront() || isOffEnd() ) {
	    insertAfterCursor(newEntry);
	} else {
	    decrementCursor();
	    insertAfterCursor(newEntry);
	    incrementCursor();
	    incrementCursor();
	    // ((TwoWayNode)cursorNode_).insertBefore(newEntry);
	    // length_ ++;
	}
    }
    public /*@ non_null @*/ Object clone() {
	return(new TwoWayList(this));
    }
    public TwoWayIterator createIterator() {
	// System.out.println("creating:" + toString());
	return new TwoWayIterator( (TwoWayNode) theListNode_ );
    }

    // ***********************************************************
    // protected methods

    protected TwoWayList(TwoWayList othLst) {
	theListNode_ = (TwoWayNode) othLst.theListNode_.clone();
	length_ = othLst.length_;
	cursorNode_ = theListNode_;

	// set the lastNode_ field
	lastNode_ = (TwoWayNode) theListNode_;
	while (lastNode_.getNextNode() != null) {
	    lastNode_ = (TwoWayNode) lastNode_.getNextNode();
	}

	// To satisfy the class invariant the 
	// model field 'cursor' needs a valid value before the call!

	firstEntry();
    }

}
