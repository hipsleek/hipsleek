// @(#) $Id: OneWayList.java,v 1.2 2009-02-17 08:55:21 chinwn Exp $

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

//@ refine "OneWayList.jml";

import org.jmlspecs.samples.list.node.OneWayNode;

//@ model import org.jmlspecs.models.JMLObjectSequence;

// FIXME: adapt this file to non-null-by-default and remove the following modifier.
/*@ nullable_by_default @*/ 
public class OneWayList { // Singly Linked List

    // data members

    protected OneWayNode theListNode_;

    // used for inserting and iteration through the List 
    protected OneWayNode cursorNode_;

    public OneWayList() {
	theListNode_ = new OneWayNode(null);
	cursorNode_ = null;
    }

    // iteration methods
    // -----------------

    public void firstEntry() {
	// The first node is a sentinel so the first entry is in the 2nd node
	cursorNode_ = theListNode_.getNextNode();
    }
    public void incrementCursor() {
	if (isOffEnd()) {
	    // System.err.println("Error in `list2.OneWayList.incrementCursor()': No more List entries");
	    // System.err.println("List is " + this.toString());
	    throw new IllegalStateException("Error in `list2.OneWayList.incrementCursor()': No more List entries\n"
					    + "List is " + this.toString() );
	}
	cursorNode_ = cursorNode_.getNextNode();
    }
    public /*@ pure @*/ boolean isOffEnd() {
	return cursorNode_ == null;
    }
    public /*@ pure @*/ boolean isOffFront() {
	return cursorNode_ == theListNode_;
    }
    public /*@ pure @*/ Object getEntry() {
	if (isOffEnd() || isOffFront()) {
	    // The method cannot be pure if it calls the following
	    //System.err.println("Error in `list2.OneWayList.getEntry': cursorNode_ is invalid");
	    //System.err.println(this);
	    throw new IllegalStateException("Error in `list2.OneWayList.getEntry': cursorNode_ is invalid\n"
					    + "List is " + this.toString() );
	}
	return cursorNode_.getEntry();
    }

    // methods for changing the list
    // -----------------------------
    public void removeEntry() {
	if (isOffEnd() || isOffFront()) {
	    // System.err.println("Error in `list2.OneWayList.removeEntry': cursorNode_ is invalid");
	    // System.err.println("List is " + this.toString());
	    throw new IllegalStateException("Error in `list2.OneWayList.removeEntry()': cursorNode_ is invalid\n"
					    + "List is " + this.toString() );
	}

	// link the previous node to the next node
	cursorNode_ = previousNode(theListNode_, cursorNode_);
	cursorNode_.removeNextNode();
    }
    public void replaceEntry(Object newEntry) {
	cursorNode_.setEntry(newEntry);
    }
    public void insertAfterCursor(Object newEntry) {
	if (isOffEnd()) {
	    // System.err.println("Error in `list2.OneWayList.insertAfterCursor': cursorNode_ is invalid");
	    // System.err.println("Attempting to insert " + newEntry);
	    // System.err.println("into list " + this.toString());
	    throw new IllegalStateException("Error in `list2.OneWayList.insertAfterCursor()': cursorNode_ is invalid\n"
					    + "Attempting to insert " + newEntry
					    + "into list " + this.toString() );
	}

	// creat a new Node containing newEntry and insert after cursor
	cursorNode_.insertAfter(newEntry);
    }
    public void insertBeforeCursor(Object newEntry) {
	if (isOffFront()) {
	    // System.err.println("Error in `list2.OneWayList.insertBeforeCursor': cursorNode_ is invalid");
	    // System.err.println("Attempting to insert " + newEntry);
	    // System.err.println("into list " + this.toString());
	    throw new IllegalStateException("Error in `list2.OneWayList.insertBeforeCursor()': cursorNode_ is invalid\n"
					    + "Attempting to insert " + newEntry
					    + "into list " + this.toString() );
	}

	cursorNode_ = previousNode(theListNode_, cursorNode_);

	// link previous Node to new Node
	insertAfterCursor(newEntry);

	// move the cursor forward to the original Node
	incrementCursor();
	incrementCursor();
    }
    public /*@ non_null @*/ Object clone() {
	return new OneWayList(this);
    }
    public /*@ non_null @*/ String toString() {
	String str = "<";
	OneWayNode curr = theListNode_.getNextNode();
	while (curr != cursorNode_ && curr != null) {
	    str += curr.getEntry().toString();
	    curr = curr.getNextNode();
	    if (curr.hasNext()) {
		str += ", ";
	    }
	}
	str += " || ";
	while (curr != null) {
	    str += curr.getEntry().toString();
	    curr = curr.getNextNode();
	    if (curr.hasNext()) {
		str += ", ";
	    }
	}
	str += ">";
	return str;
    }

    // ***********************************************************
    // protected methods

    protected OneWayNode previousNode(OneWayNode curr, OneWayNode node) {
	if (curr.getNextNode() == node) {
	    return curr;
	} else {
	    return previousNode(curr.getNextNode(), node);
	}
    }
    protected OneWayList(OneWayList othLst) {
	theListNode_ = (OneWayNode) othLst.theListNode_.clone();
	firstEntry();
    }

}
