/**
 Display module to populate content of the HTML
 @author Vu An Hoa
 */

function getHTML(obj) {
	var result = "<div class=\"toggle_on_click " + obj.type + "\"";
	if (obj.type == "proc") {
		result += " id=\"content-proc-" + obj.name + "\">";
	} else if (obj.type == "precnd_arracc") {
		result += ">" + "Array access";
	} else if (obj.type == "precnd_arrupdt") {
		result += ">" + "Array update";
	} else if (obj.type == "precnd") {
		result += ">" + "Procedure call";
	}	else if (obj.type == "post") {
		result += ">" + "Post-condition";
	} else if (obj.type == "assert") {
		result += ">" + "Assertion";
	} else if (obj.type == "pureimply") {
		result += ">" + obj.formula;
	} else result += ">";
	result += "<div class=\"childs\">";
	if (obj.childs != null) {
		for(var i = 0; i < obj.childs.length; i++) {
			result += getHTML(obj.childs[i]);
		}
	}
	result += "</div>";
	result += "</div>";
	return result;
}

var currently_displayed_id = "";

// Set up the HTML DOM
function setup() {
	// Set the file name in the header
	$("#header").html(srcfilename);

	// Generate HTML content and set up the navigation panel with appropriate call back functions
	var content_proc = "";
	for(i = 0; i < jsonproof.length; i++) {
		var p = jsonproof[i];
		if (p.type == "proc") {
			content_proc += getHTML(p);
			var navid = "nav-proc-" + p.name;
			$("#nav-proc-list").append("<li><span id=\"" + navid + "\">" + p.name + "</span></li>");
			$("#" + navid).click(function(){
				var orgid = this.id.substring("3");
				if (currently_displayed_id != "") {
					$("#content"+currently_displayed_id).hide();
					$("#nav"+currently_displayed_id).removeClass("selected");
				}
				$("#"+this.id).addClass("selected");
				$("#content"+orgid).show();
				currently_displayed_id = orgid;
			});
		}
	}
	$("#content-proc").html(content_proc);
	for(i = 0; i < jsonproof.length; i++) {
		var p = jsonproof[i];
		if (p.type == "proc") {
			$("#content-proc-" + p.name).hide();
		}
	}
}

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


