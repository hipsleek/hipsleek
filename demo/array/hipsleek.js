/*
 Script obtained from http://www.ridgway.co.za/archive/2005/10/30/asimplecssbasedtreeview.aspx
 */

Array.prototype.indexOf = IndexOf;

//Toggles between two classes for an element
function ToggleClass(element, firstClass, secondClass, event)
{
    event.cancelBubble = true;
    
    var classes = element.className.split(" ");
    var firstClassIndex = classes.indexOf(firstClass);
    var secondClassIndex = classes.indexOf(secondClass);
    
    if (firstClassIndex == -1 && secondClassIndex == -1)
    {
        classes[classes.length] = firstClass;
    }
    else if (firstClassIndex != -1)
    {
        classes[firstClassIndex] = secondClass;
    }
    else
    {
        classes[secondClassIndex] = firstClass;
    }
    
    element.className = classes.join(" ");
    
}

//Finds the index of an item in an array
function IndexOf(item)
{
    for (var i=0; i < this.length; i++)
    {        
        if (this[i] == item)
        {
            return i;
        }
    }
    
    return -1;
}

//The toggle event handler for each expandable/collapsable node
//- Note that this also exists to prevent any IE memory leaks 
//(due to circular references caused by this)
function ToggleNodeStateHandler(event)
{
    ToggleClass(this, "Collapsed", "Expanded", (event == null) ? window.event : event);
}

//Prevents the onclick event from bubbling up to parent elements
function PreventBubbleHandler(event)
{
    if (!event) event = window.event;
    event.cancelBubble = true;
}

//Adds the relevant onclick handlers for the nodes in the tree view
function SetupTreeView(elementId)
{
    var tree = document.getElementById(elementId);
    var treeElements = tree.getElementsByTagName("li");
    
    for (var i=0; i < treeElements.length; i++)
    {
        if (treeElements[i].getElementsByTagName("ul").length > 0)
        {
            treeElements[i].onclick = ToggleNodeStateHandler; 
        }
        else
        {
            treeElements[i].onclick = PreventBubbleHandler; 
        }
    }
}


