// @(#) $Id: E_OneWayList.java,v 1.1.1.1 2008-03-15 06:55:00 nguyenh2 Exp $

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

//@ refine "E_OneWayList.jml";

import org.jmlspecs.samples.list.node.OneWayNode;

// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public class E_OneWayList extends OneWayList { // Singly Linked List

    // data members
    protected int length_;

    public E_OneWayList() {
	super();
	length_ = 0;
    }

    // accessors
    // ---------
    public /*@ pure @*/ int length() {
	return length_;
    }
    public /*@ pure @*/ boolean isEmpty() {
	return length_ == 0;
    }
    public /*@ pure @*/ boolean equals(/*@ nullable @*/ Object obj) {
	if (! (obj instanceof OneWayList) ) {
	    return false;
	} else {
	    return equalsNode(theListNode_, 
		              ((OneWayList)obj).theListNode_);
	}
    }

    public /*@ pure @*/ int hashCode() {
        if ( isEmpty() ) {
            return super.hashCode();
        } else {
            return theListNode_.getNextNode().getEntry().hashCode() + length();
        }
    }

    // methods for changing the list
    // -----------------------------
    public void removeEntry() {
	super.removeEntry();
	length_ --;
    }
    public void insertAfterCursor(Object newEntry) {
	super.insertAfterCursor(newEntry);
	length_ ++;
    }
    public void insertBeforeCursor(Object newEntry) {
	cursorNode_ = previousNode(theListNode_, cursorNode_);
	cursorNode_.insertAfter(newEntry);
	incrementCursor();
	incrementCursor();
	length_ ++;
    }
    public void append(Object newEntry) {
	lastEntry();
	if (isOffEnd()) { // empty list is always off the end!
	    insertBeforeCursor(newEntry);
	} else {
	    insertAfterCursor(newEntry);
	    incrementCursor();
	}
    }
    public void removeAllEntries() {
	firstEntry();
	while (!isOffEnd()) {
	    removeEntry();
	    incrementCursor();
	}
    }
    public /*@ non_null @*/ Object clone() {
	return new E_OneWayList(this);
    }

    // ***********************************************************
    // protected methods

    protected void lastEntry() {
	if (isOffEnd()) {
	    cursorNode_ = theListNode_;
	}
	while (cursorNode_.getNextNode() != null) {
	    incrementCursor();
	}
    }
    protected E_OneWayList(E_OneWayList othLst) {
	super(othLst);
	length_ = othLst.length();
    }
    private /*@ pure @*/ boolean equalsNode(/*@ nullable @*/ OneWayNode nd1, /*@ nullable @*/ OneWayNode nd2) {
	if (nd1 == null && nd2 == null) {
	    return true;
	} else if (nd1 == null || nd2 == null) {
	    return false;
	} else if (nd1.getEntry() == nd2.getEntry()) {
	    if (nd1 == nd2) {
		return false;
	    } else {
		return equalsNode(nd1.getNextNode(), nd2.getNextNode());
	    }
	} else {
	    return false;
	}
    }
}
